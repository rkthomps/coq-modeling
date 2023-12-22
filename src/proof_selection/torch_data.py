from typing import Any
from dataclasses import dataclass
import json

import torch
from torch.utils.data import Dataset
from transformers import AutoTokenizer, ByT5Tokenizer


from proof_selection.proof_selection_example import ProofSelectionExample
from tactic_gen.proof_distance import levenshtein_dist_fast 


@dataclass
class ProofRetBatch:
    candidate_ids: torch.Tensor
    candidate_mask: torch.Tensor
    context_ids: torch.Tensor
    context_mask: torch.Tensor
    label: torch.Tensor


def tokenize_strings(
    tokenizer: ByT5Tokenizer, strings: list[str], max_seq_len: int
) -> Any:
    return tokenizer(
        strings,
        padding="longest",
        max_length=max_seq_len,
        truncation=True,
        return_tensors="pt",
    )


class ProofRetDataset(Dataset):
    def __init__(
        self, data_loc: str, tokenizer: ByT5Tokenizer, max_seq_len: int
    ) -> None:
        self.tokenizer = tokenizer
        self.examples: list[str] = []
        self.max_seq_len = max_seq_len
        with open(data_loc, "r") as fin:
            for line in fin:
                self.examples.append(line)

    def __len__(self) -> int:
        return len(self.examples) * (len(self.examples) - 1)

    def __getitem__(self, index: int) -> ProofRetBatch:
        pass_idx = index // len(self.examples)
        left_idx = index % len(self.examples)
        # TODO
        left_data = json.loads(self.examples[left_idx])
        left_obj = ProofSelectionExample.from_json(left_data)

        right_idx = (left_idx + pass_idx + 1) % len(self.examples)
        right_data = json.loads(self.examples[right_idx])
        right_obj = ProofSelectionExample.from_json(right_data)

        left_token_batch = tokenize_strings(
            self.tokenizer, [left_obj.candidate_proof], self.max_seq_len
        )
        right_token_batch = tokenize_strings(
            self.tokenizer, [right_obj.current_context], self.max_seq_len
        )
        target = levenshtein_dist_fast(left_obj.norm_steps, right_obj.norm_steps)
        norm_target = target / max(len(left_obj.norm_steps), len(right_obj.norm_steps)) 

        return ProofRetBatch(
            left_token_batch.input_ids, 
            left_token_batch.attention_mask,
            right_token_batch.input_ids, 
            right_token_batch.attention_mask,
            torch.tensor([norm_target])
        )
