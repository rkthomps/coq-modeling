from __future__ import annotations
from typing import Any, Optional, Mapping

import torch
from transformers import (
    PreTrainedModel,
    PretrainedConfig,
    T5Config,
    T5ForConditionalGeneration,
)
from transformers.modeling_outputs import (
    BaseModelOutputWithPastAndCrossAttentions,
    Seq2SeqLMOutput,
)


class FidCombinedConfig(T5Config):
    def __init__(self, n_passages: int = 0, **kwargs: Any):
        super(FidCombinedConfig, self).__init__(**kwargs)
        self.n_passages = n_passages

    @classmethod
    def from_t5_config(cls, n_passages: int, t5_conf: T5Config) -> FidCombinedConfig:
        return cls(n_passages, **t5_conf.__dict__)


class FidCombined(T5ForConditionalGeneration):
    def __init__(self, config: FidCombinedConfig):
        super(FidCombined, self).__init__(config)
        self.config = config
        self.act = torch.nn.ReLU()
        # self.projector = torch.nn.Linear(
        #     config.d_model * config.n_passages, config.d_model
        # )

    def forward(
        self,
        input_ids: Optional[torch.Tensor] = None,
        attention_mask: Optional[torch.Tensor] = None,
        labels: Optional[torch.Tensor] = None,
        decoder_input_ids: Optional[torch.Tensor] = None,
        encoder_outputs: Optional[BaseModelOutputWithPastAndCrossAttentions] = None,
        **kwargs: Any,
    ):
        """
        B = Batch size
        N = Number of passages
        L = Passage length
        D = Hidden dimension

        input_ids:      B x N x L
        attention_mask: B x N x L
        """
        # Run the encoder during training and on the first
        # iteration of inference.
        # print(
        #     "memory",
        #     torch.cuda.memory_allocated() / torch.cuda.max_memory_allocated(),
        # )
        # print("allocated", torch.cuda.memory_allocated())
        # print("max", torch.cuda.max_memory_allocated())
        if encoder_outputs is None:
            assert input_ids is not None
            assert attention_mask is not None
            batch_size, n_passages, seq_len = input_ids.size()
            assert n_passages == self.config.n_passages

            last_hidden_states_list: list[torch.Tensor] = []
            for i in range(n_passages):
                for p in self.encoder.parameters():
                    if p.grad is not None:
                        print("grad", p.grad.shape)
                        break
                print(i, torch.cuda.memory_allocated())
                passage_i_outputs: BaseModelOutputWithPastAndCrossAttentions = (
                    self.encoder(input_ids[:, i, :], attention_mask[:, i, :])
                )
                passage_i_last_state = passage_i_outputs.last_hidden_state  # B x L x D
                last_hidden_states_list.append(passage_i_last_state[:, None, :, :])

            expanded_encoder_last_state = torch.concat(
                last_hidden_states_list, dim=1
            )  # (B x N x L x D)

            # bn_input_ids = input_ids.view(-1, input_ids.size(-1))  # (B * N) x L
            # bn_attention_mask = attention_mask.view(-1, attention_mask.size(-1))
            # raw_encoder_outputs: BaseModelOutputWithPastAndCrossAttentions = (
            #     self.encoder(bn_input_ids, bn_attention_mask)
            # )
            # bn_encoder_last_state = (
            #     raw_encoder_outputs.last_hidden_state
            # )  # (B * N) x L x D
            # expanded_encoder_last_state = bn_encoder_last_state.view(
            #     batch_size, n_passages, seq_len, -1
            # )  # B x N x L x D

            bl_encoder_last_state = expanded_encoder_last_state.transpose(
                1, 2
            )  # B x L x N x D
            bl_attention_mask = attention_mask.transpose(1, 2)  # B x L x N
            zeros = torch.zeros(
                (batch_size, seq_len, n_passages, self.config.d_model),
                device=self.device,
            )
            project_mask = torch.where(
                bl_attention_mask[..., None] == 1, bl_encoder_last_state, zeros
            )  # B x L x N x D
            masked_last_state = project_mask.reshape(
                (batch_size, seq_len, n_passages * self.config.d_model)
            )  # B x L x (N * D)

            # proj_last_states_list: list[torch.Tensor] = []
            # for i in range(seq_len):
            #     proj_last_state_i = self.act(self.projector(masked_last_state[:, i, :]))
            #     proj_last_states_list.append(proj_last_state_i[:, None, :])
            # proj_last_state = torch.concat(proj_last_states_list, dim=1)

            # proj_last_state = self.act(self.projector(masked_last_state))  # B x L x D
            proj_last_state = expanded_encoder_last_state[:, 0, :, :]
            updated_attn_mask = attention_mask.any(dim=1)
            encoder_outputs = BaseModelOutputWithPastAndCrossAttentions(proj_last_state)

            # Sanity check
            # updated_attn_mask = attention_mask[:, 0, :]
            # copied_ids = input_ids[:, 0, :].clone()
            # copied_mask = attention_mask[:, 0, :].clone()
            # encoder_outputs = self.encoder(copied_ids, copied_mask)

        else:
            updated_attn_mask = attention_mask
            if updated_attn_mask is not None:
                assert updated_attn_mask.dim() == 2

        if decoder_input_ids is None:
            decoder_input_ids = self._shift_right(labels)

        assert encoder_outputs is not None
        decoder_out: BaseModelOutputWithPastAndCrossAttentions = self.decoder(
            decoder_input_ids,
            encoder_hidden_states=encoder_outputs.last_hidden_state,
            encoder_attention_mask=updated_attn_mask,
        )

        sequence_outputs = decoder_out.last_hidden_state
        lm_logits: torch.FloatTensor = self.lm_head(sequence_outputs)

        loss: Optional[torch.FloatTensor] = None
        if labels is not None:
            loss_fct = torch.nn.CrossEntropyLoss(ignore_index=-100)
            # move labels to correct device to enable PP
            labels = labels.to(lm_logits.device)
            loss = loss_fct(lm_logits.view(-1, lm_logits.size(-1)), labels.view(-1))
            print("loss:", loss)

        return Seq2SeqLMOutput(
            loss=loss,
            logits=lm_logits,
            past_key_values=decoder_out.past_key_values,
            decoder_hidden_states=decoder_out.hidden_states,
            decoder_attentions=decoder_out.attentions,
            cross_attentions=decoder_out.cross_attentions,
            encoder_last_hidden_state=encoder_outputs.last_hidden_state,
            encoder_hidden_states=encoder_outputs.hidden_states,
            encoder_attentions=encoder_outputs.attentions,
        )

    def load_t5(self, state_dict: Mapping[str, Any]):
        self.load_state_dict(state_dict)

    def generate(
        self,
        input_ids: torch.Tensor,
        attention_mask: torch.Tensor,
        max_length: int,
        **kwargs: Any,
    ):
        return super().generate(
            input_ids=input_ids.view(input_ids.size(0), -1),
            attention_mask=attention_mask.view(attention_mask.size(0), -1),
            max_length=max_length,
            **kwargs,
        )
