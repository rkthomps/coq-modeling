from __future__ import annotations
from typing import Any

from pathlib import Path
from dataclasses import dataclass

from lemma_gen.lemma_example import LemmaExample
from lemma_gen.lemma_data import (
    ExampleCollator,
    example_collator_conf_from_yaml,
    example_collator_from_conf,
    get_tokenizer,
)
from lemma_gen.train_decoder import get_model
import yaml

from util.constants import LEMMA_DATA_CONF_NAME, TRAINING_CONF_NAME
from util.train_utils import get_required_arg

from transformers import PreTrainedModel, PreTrainedTokenizer
import torch


@dataclass
class LemmaDecoderWrapper:
    model: PreTrainedModel
    tokenizer: PreTrainedTokenizer
    collator: ExampleCollator
    hard_seq_len: int

    def get_lemmas(self, example: LemmaExample, n: int) -> list[str]:
        collated_input = self.collator.collate_input(self.tokenizer, example)
        inputs = self.tokenizer(
            collated_input,
            max_length=self.hard_seq_len,
            truncation=True,
            return_tensors="pt",
        )
        with torch.no_grad():
            outputs = self.model.generate(
                inputs["input_ids"],
                max_new_tokens=1024,
                num_return_sequences=n,
                return_dict_in_generate=True,
                output_scores=True,
                length_penalty=0,
                temperature=1,
                do_sample=True,
            )
            input_num_tokens = inputs["input_ids"].shape[1]
            generated_seqs = outputs.sequences[:, input_num_tokens:]
            lemmas = self.tokenizer.batch_decode(
                generated_seqs, skip_special_tokens=True
            )
        return lemmas

    @classmethod
    def get_training_conf(cls, checkpoint_loc: Path) -> Any:
        training_conf_loc = checkpoint_loc.parent / TRAINING_CONF_NAME
        with training_conf_loc.open("r") as fin:
            training_conf = yaml.safe_load(fin)
        return training_conf

    @classmethod
    def from_checkpoint(cls, checkpoint_loc: Path) -> LemmaDecoderWrapper:
        training_conf = cls.get_training_conf(checkpoint_loc)
        hard_seq_length = get_required_arg("hard_seq_len", training_conf)
        example_collator_conf = example_collator_conf_from_yaml(
            training_conf["example_collator"]
        )
        example_collator = example_collator_from_conf(example_collator_conf)
        tokenizer = get_tokenizer(
            get_required_arg("model_name", training_conf), add_eos=False
        )
        model = get_model(str(checkpoint_loc.resolve()))
        return cls(model, tokenizer, example_collator, hard_seq_length)
