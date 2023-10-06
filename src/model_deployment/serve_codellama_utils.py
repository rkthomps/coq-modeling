
from __future__ import annotations
from typing import Any

from transformers import (
    StoppingCriteria, CodeLlamaTokenizer, 
    LlamaForCausalLM, StoppingCriteriaList,)
from transformers.generation.utils import SampleDecoderOnlyOutput
import torch
from torch import LongTensor, FloatTensor

device = "cuda" if torch.cuda.is_available() else "cpu"

class PeriodStoppingCriteria(StoppingCriteria):
    def __init__(self, stop_tok_ids: list[int]) -> None:
        self.stop_tok_ids = stop_tok_ids
        self.num_input_periods = torch.tensor(0).to(device)

    def set_num_periods(self, input_ids: LongTensor) -> None:
        self.num_input_periods = self.get_num_periods(input_ids)[0]

    def get_num_periods(self, input_ids: LongTensor) -> torch.Tensor:
        start_shape = (input_ids.shape[0],)
        sum_input_periods = torch.full(start_shape, fill_value=0).to(device)
        for stop_tok_id in self.stop_tok_ids:
            sum_input_periods += (input_ids == stop_tok_id).sum(axis=1)
        return sum_input_periods

    def __call__(self, input_ids: LongTensor, scores: FloatTensor, **kwargs: Any) -> bool:
        return bool((self.get_num_periods(input_ids) > self.num_input_periods).all())

    @classmethod
    def from_tokenizer(cls, tokenizer: CodeLlamaTokenizer) -> PeriodStoppingCriteria:
        period_tok_ids: list[int] = []
        for token, token_id in tokenizer.get_vocab().items():
            if "." in token:
                period_tok_ids.append(token_id)
        return cls(period_tok_ids)


def get_sequence_score(input_sequence: torch.LongTensor,
                       whole_sequence: torch.LongTensor, 
                       scores: tuple[torch.FloatTensor],
                       stop_criteria: PeriodStoppingCriteria) -> float:
    assert len(scores) == int(whole_sequence.shape[0] - input_sequence.shape[0])
    sequence_score = 0
    start_idx = whole_sequence.shape[0] - len(scores)
    stop_criteria.set_num_periods(input_sequence[None, :])
    for i in range(len(scores)):
        index = whole_sequence[start_idx + i] 
        score_at_i = scores[i][0, index] - torch.logsumexp(scores[i][0], axis=0)
        sequence_score += (score_at_i)
        if stop_criteria(whole_sequence[None, :(start_idx + i + 1)], scores):
            break
    return float(sequence_score)

class SampleResult:
    def __init__(self, tactics: list[str], scores: list[float], num_tokens: list[int]) -> None:
        assert all([type(t) == str for t in tactics])
        assert all([type(s) == float for s in scores])
        assert all([type(t) == int for t in num_tokens])
        self.tactics = tactics
        self.scores = scores
        self.num_tokens = num_tokens

    def to_json(self) -> Any:
        return {
            "tactics": self.tactics,
            "scores": self.scores,
            "num_tokens": self.num_tokens
        }

    @classmethod
    def from_json(cls, json_data: Any) -> SampleResult:
        tactics = json_data["tactics"]
        scores = json_data["scores"]
        num_tokens = json_data["num_tokens"]
        return cls(tactics, scores, num_tokens)


def do_sample(input_ids: torch.LongTensor, 
              model: LlamaForCausalLM,
              tokenizer: CodeLlamaTokenizer,
              n_recs: int,
              period_stopping: PeriodStoppingCriteria) -> SampleResult:
    period_stopping.set_num_periods(input_ids)
    stopping_list = StoppingCriteriaList([period_stopping])
    tactics: list[str] = []
    scores: list[float] = []
    num_tokens: list[int] = []
    for i in range(n_recs):
        output = model.generate(
            input_ids,
            temperature=1,
            do_sample=True,
            max_new_tokens=32,
            output_scores=True,
            return_dict_in_generate=True,
            stopping_criteria=stopping_list,
        )
        assert type(output) == SampleDecoderOnlyOutput 
        output_sequence = output.sequences[0]
        input_sequence = input_ids[0]
        output_length = len(output.scores)
        tactic = tokenizer.decode(output_sequence[len(input_sequence):], skip_special_tokens=True)
        score = get_sequence_score(input_sequence, output_sequence, output.scores, period_stopping)
        tactics.append(tactic)
        scores.append(score)
        num_tokens.append(output_length)
    return SampleResult(tactics, scores, num_tokens)
    
     