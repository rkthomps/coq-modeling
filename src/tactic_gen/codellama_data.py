from typing import Any, Optional

from torch.utils.data import Dataset
from transformers import CodeLlamaTokenizer, BatchEncoding
from trl import DataCollatorForCompletionOnlyLM
import jsonlines
from typeguard import typechecked

from tactic_gen.lm_example import LmExample

# FROM HERE: https://huggingface.co/docs/trl/sft_trainer#train-on-completions-only
RESPONSE_TEMPLATE = "<TACTIC>"
NEWLINE_RESPONSE_TEMPLATE = f"\n{RESPONSE_TEMPLATE}\n"


def collate_example(
    tokenizer: CodeLlamaTokenizer,
    max_input_len: int,
    max_seq_len: int,
    input: str,
    output: str,
    response_template: str = NEWLINE_RESPONSE_TEMPLATE,
) -> tuple[str, str]:
    whole_input_string = f"{input}{response_template}"
    input_suffix = tokenizer.encode(whole_input_string)[(-1 * max_input_len) :]
    final_input_str = tokenizer.decode(input_suffix, skip_special_tokens=True)
    remaining_toks = max_seq_len - len(input_suffix)
    output_prefix = tokenizer.encode(output)[:remaining_toks]
    final_output_str = tokenizer.decode(output_prefix)
    return final_input_str, final_output_str


@typechecked
class LmDataset(Dataset):
    def __init__(
        self,
        data_path: str,
        tokenizer: CodeLlamaTokenizer,
        max_input_len: int,
        max_seq_len: int,
        max_n_examples: Optional[int] = None,
    ) -> None:
        self.raw_examples: list[LmExample] = []
        response_template_ids = tokenizer.encode(NEWLINE_RESPONSE_TEMPLATE)[2:-1]
        self.collator = DataCollatorForCompletionOnlyLM(
            response_template_ids, tokenizer=tokenizer
        )
        self.tokenizer = tokenizer
        self.max_input_len = max_input_len
        self.max_seq_len = max_seq_len
        with jsonlines.open(data_path) as fin:
            for i, obj in enumerate(fin):
                print(f"\rLoading example: {i}", end="")
                self.raw_examples.append(LmExample.from_json(obj))
                if max_n_examples and len(self.raw_examples) >= max_n_examples:
                    break

    def __len__(self) -> int:
        return len(self.raw_examples)

    def __getitem__(self, idx: int) -> BatchEncoding:
        target_lm_example = self.raw_examples[idx]
        clean_in, clean_out = collate_example(
            self.tokenizer,
            self.max_input_len,
            self.max_seq_len,
            target_lm_example.input,
            target_lm_example.output,
        )
        clean_example = f"{clean_in}{clean_out}"
        return self.tokenizer(
            clean_example, max_length=self.max_seq_len, truncation=True
        )
