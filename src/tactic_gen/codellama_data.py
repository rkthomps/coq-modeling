from typing import Any, Optional
from pathlib import Path
import json

from torch.utils.data import Dataset
from transformers import CodeLlamaTokenizer, BatchEncoding
from trl import DataCollatorForCompletionOnlyLM
import jsonlines
from typeguard import typechecked
from data_management.jsonl_utils import ExampleDB

from tactic_gen.lm_example import LmExample

# FROM HERE: https://huggingface.co/docs/trl/sft_trainer#train-on-completions-only
RESPONSE_TEMPLATE = "<TACTIC>"
NEWLINE_RESPONSE_TEMPLATE = f"\n{RESPONSE_TEMPLATE}\n"


def collate_example(
    tokenizer: CodeLlamaTokenizer,
    max_num_passages: int,
    max_tokens_per_passage: int,
    max_input_len: int,
    max_seq_len: int,
    example: LmExample,
    response_template: str = NEWLINE_RESPONSE_TEMPLATE,
) -> tuple[str, str]:
    passage_strs: list[str] = []
    if example.passages is not None:
        for passage in example.passages[:max_num_passages]:
            passage_toks = tokenizer.encode(passage)[:max_tokens_per_passage]
            passage_str = tokenizer.decode(passage_toks, skip_special_tokens=True)
            passage_strs.append(passage_str)

    final_passages_str = "\n\n".join(passage_strs)

    input_str = f"{example.input}{response_template}"
    input_suffix = tokenizer.encode(input_str)[(-1 * max_input_len) :]
    trunc_input_str = tokenizer.decode(input_suffix, skip_special_tokens=True)
    final_input_str = f"{final_passages_str}\n\n{trunc_input_str}"
    remaining_toks = max_seq_len - (
        max_num_passages * max_tokens_per_passage + max_input_len
    )
    output_prefix = tokenizer.encode(example.output)[:remaining_toks]
    final_output_str = tokenizer.decode(output_prefix, skip_special_tokens=True)
    return final_input_str, final_output_str


class LmDataset(Dataset):
    def __init__(
        self,
        data_path: Path,
        tokenizer: CodeLlamaTokenizer,
        max_num_passages: int,
        max_tokens_per_passage: int,
        max_input_len: int,
        max_seq_len: int,
        max_n_examples: Optional[int] = None,
    ) -> None:
        self.edb = ExampleDB.load(data_path)
        self.raw_examples: list[LmExample] = []
        response_template_ids = tokenizer.encode(NEWLINE_RESPONSE_TEMPLATE)[2:-1]
        self.collator = DataCollatorForCompletionOnlyLM(
            response_template_ids, tokenizer=tokenizer
        )
        self.tokenizer = tokenizer
        self.max_num_passages = max_num_passages
        self.max_tokens_per_passage = max_tokens_per_passage
        self.max_input_len = max_input_len
        self.max_seq_len = max_seq_len
        self.max_n_examples = max_n_examples

    def __len__(self) -> int:
        if self.max_n_examples is not None:
            return self.max_n_examples
        return self.edb.size()

    def __getitem__(self, idx: int) -> BatchEncoding:
        target_lm_example = LmExample.from_json(json.loads(self.edb.retrieve(idx + 1)))
        clean_in, clean_out = collate_example(
            self.tokenizer,
            self.max_num_passages,
            self.max_tokens_per_passage,
            self.max_input_len,
            self.max_seq_len,
            target_lm_example,
        )
        clean_example = f"{clean_in}{clean_out}"
        return self.tokenizer(
            clean_example, max_length=self.max_seq_len, truncation=True
        )
