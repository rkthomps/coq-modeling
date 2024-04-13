from __future__ import annotations
import torch
from pathlib import Path
import yaml

from goal_evaluation.goal_example import GoalExample
from goal_evaluation.goal_data import SEP_ID, START_ID, tokenize_example
from transformers import OPTForCausalLM, GPT2Tokenizer 

from util.constants import TRAINING_CONF_NAME

class GoalWrapper:
    def __init__(self, goal_model: OPTForCausalLM, tokenizer: GPT2Tokenizer, max_seq_len: int):
        self.goal_model = goal_model
        self.tokenizer = tokenizer
        self.max_seq_len = max_seq_len
        self.sft = torch.nn.Softmax()
    
    def get_expected_n_left_and_score(self, example: GoalExample) -> tuple[float, float]:
        tokenized_input = tokenize_example(self.tokenizer, self.max_seq_len, example) 
        query = tokenized_input["input_ids"] + [SEP_ID]
        input_tensor = torch.tensor([query], device=self.goal_model.device)
        attn_mask = torch.tensor([[1 for _ in range(len(query))]], device=self.goal_model.device)
        model_inputs = {
            "input_ids": input_tensor,
            "attention_mask": attn_mask,
        }
        with torch.no_grad():
            output = self.goal_model(**model_inputs)
        n_step_logits = output.logits[0, -1, START_ID:]
        probs = self.sft(n_step_logits)
        exp_n_steps = probs @ torch.arange(len(probs), device=self.goal_model.device, dtype=torch.float32)

        loss_inputs = input_tensor[:, :-1]
        loss_output_logits = output.logits[:, :-1]
        shift_logits = loss_output_logits[0, :-1, :].contiguous()
        shift_logprobs = torch.log_softmax(shift_logits, dim=-1)
        shift_labels = loss_inputs[0, None, 1:].contiguous()
        scores = torch.gather(shift_logprobs, 1, shift_labels)
        return float(exp_n_steps), float(scores.mean())

    @classmethod
    def from_checkpoint(cls, checkpoint_loc: Path) -> GoalWrapper:
        model_training_conf_loc = checkpoint_loc.parents[0] / TRAINING_CONF_NAME
        with model_training_conf_loc.open("r") as fin:
            training_conf = yaml.load(fin, Loader=yaml.Loader)
        model = OPTForCausalLM.from_pretrained(checkpoint_loc)
        model = model.cuda()
        tokenizer = GPT2Tokenizer.from_pretrained(training_conf["model_name"], truncation_side="left")
        max_seq_len = training_conf["max_seq_len"]
        return cls(model, tokenizer, max_seq_len)
