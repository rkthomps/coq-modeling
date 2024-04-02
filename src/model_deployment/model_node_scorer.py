from __future__ import annotations

from model_deployment.node_score import NodeScore
from transformers import LlamaForCausalLM, CodeLlamaTokenizer, BitsAndBytesConfig
import torch


class ModelNodeScorer:
    def __init__(
        self,
        model: LlamaForCausalLM,
        tokenizer: CodeLlamaTokenizer,
    ):
        self.model = model
        self.tokenizer = tokenizer

    def score_proof(self, thm_text: str, proof_text: str) -> float:
        # advice = (
        #     "First destruct on the list. ",
        #     "Then, destruct on the min of the tail of the list. ",
        #     "Then, destruct on whether the head is less than the min of the tail",
        #     "Then provide witnesses for each branch."
        # )

        advice = (
            "First, unfold even and odd. Then use the witness k1 + k2 + 1. Then close the proof with lia.",
        )
        input_str = f"{advice}{thm_text}{proof_text}"
        input = self.tokenizer(input_str, return_tensors="pt")
        with torch.no_grad():
            result = self.model(
                input_ids=input.input_ids,
                attention_mask=input.attention_mask,
                labels=input.input_ids,
                return_dict=True,
            )
            probs = torch.log_softmax(result.logits, dim=2) 
            shift_probs = probs[..., :-1, :].contiguous()
            shift_labels = input.input_ids[..., 1:].contiguous()
            vocab_size = shift_probs.shape[-1]
            scores = torch.gather(shift_probs, dim=2, index=shift_labels[:, :, None]).squeeze()
            total_score = scores.sum()
            return float(total_score - len(scores) * torch.log(torch.tensor(0.9)))


            return float(result.loss)

    @classmethod
    def from_name(cls, model_name: str) -> ModelNodeScorer:
        quant_conf = BitsAndBytesConfig(
            load_in_4bit=True, bnb_4bit_compute_dtype=torch.float16
        )
        model = LlamaForCausalLM.from_pretrained(
            model_name,
            quantization_config=quant_conf,
        )
        tokenizer = CodeLlamaTokenizer.from_pretrained(model_name)
        return cls(model, tokenizer)
