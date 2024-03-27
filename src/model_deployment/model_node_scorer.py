

from model_deployment.node_score import NodeScore
from transformers import LlamaForCausalLM, CodeLlamaTokenizer


class ModelNodeScorer:
    def __init__(self, model: LlamaForCausalLM, tokenizer: CodeLlamaTokenizer, score_type: type[NodeScore]):
        self.model = model
        self.tokenizer = tokenizer
        self.score_type = score_type
    
    def score_proof(self, thm_text: str, proof_text: str) -> float:
        input = f"{thm_text}{proof_text}"
        