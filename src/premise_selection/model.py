
from transformers import ByT5Tokenizer, T5EncoderModel
import pytorch_lightning as pl  
import torch
import torch.nn.functional as F

class PremiseRetriever(pl.LightningModule):
    def __init__(self,
                 model_name: str,
                 lr: float,
                 warmup_steps: int,
                 max_seq_len: int,
                 num_retrieved: int):
        assert type(model_name) == str
        assert type(lr) == float
        assert type(warmup_steps) == int
        assert type(max_seq_len) == int
        assert type(num_retrieved) == int
        self.model_name = model_name
        self.lr = lr
        self.warmup_steps = warmup_steps
        self.max_seq_len = max_seq_len
        self.num_retrieved = num_retrieved

        self.tokenizer = ByT5Tokenizer.from_pretrained(model_name)
        self.encoder = T5EncoderModel.from_pretrained(model_name)


    def _encode(self, input_ids: torch.Tensor, mask: torch.Tensor) -> torch.Tensor:
        ## TODO: COULD ADD SOME SORT OF "CPU CHECKPOINTING"
        hidden_states = self.encoder(
            input_ids=input_ids,
            attention_mask=mask,
            return_dict=True,
        ).last_hidden_state

        lens = mask.sum(axis=1)
        raise ValueError("Examine shapes")
        features = hidden_states * mask 
        # get some sort of avg


    def forward(self,
                context_ids: torch.Tensor,
                context_mask: torch.Tensor,
                premise_ids: torch.Tensor,
                premise_mask: torch.Tensor,
                label: torch.Tensor,
                ) -> torch.Tensor: 
        context_embs = self._encode(context_ids, context_mask)
        premise_embs = self._encode(premise_ids, premise_mask)
        similarity = torch.mm(context_embs, premise_embs.t())
        assert -1 <= similarity.min() <= similarity.max() <= 1
        loss = F.mse_loss(similarity, label) 
        return loss

    