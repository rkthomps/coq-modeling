from __future__ import annotations
from typing import Any, Optional
import heapq

from transformers import (
    StoppingCriteria,
    CodeLlamaTokenizer,
    LlamaForCausalLM,
    StoppingCriteriaList,
)
from transformers.generation.utils import SampleDecoderOnlyOutput
import torch
from torch import LongTensor, FloatTensor
from torch.nn import functional as F

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

    def __call__(
        self, input_ids: LongTensor, scores: FloatTensor, **kwargs: Any
    ) -> bool:
        return bool((self.get_num_periods(input_ids) > self.num_input_periods).all())

    @classmethod
    def from_tokenizer(cls, tokenizer: CodeLlamaTokenizer) -> PeriodStoppingCriteria:
        period_tok_ids: list[int] = []
        for token, token_id in tokenizer.get_vocab().items():
            if "." in token:
                period_tok_ids.append(token_id)
        return cls(period_tok_ids)


def get_sequence_score(
    input_sequence: torch.LongTensor,
    whole_sequence: torch.LongTensor,
    scores: tuple[torch.FloatTensor],
    stop_criteria: PeriodStoppingCriteria,
) -> float:
    assert len(scores) == int(whole_sequence.shape[0] - input_sequence.shape[0])
    sequence_score = 0
    start_idx = whole_sequence.shape[0] - len(scores)
    stop_criteria.set_num_periods(input_sequence[None, :])
    for i in range(len(scores)):
        index = whole_sequence[start_idx + i]
        score_at_i = scores[i][0, index] - torch.logsumexp(scores[i][0], axis=0)
        sequence_score += score_at_i
        if stop_criteria(whole_sequence[None, : (start_idx + i + 1)], scores):
            break
    return float(sequence_score)


class SampleResult:
    def __init__(
        self, tactics: list[str], scores: list[float], num_tokens: list[int]
    ) -> None:
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
            "num_tokens": self.num_tokens,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> SampleResult:
        tactics = json_data["tactics"]
        scores = json_data["scores"]
        num_tokens = json_data["num_tokens"]
        return cls(tactics, scores, num_tokens)


def do_sample(
    input_ids: torch.LongTensor,
    model: LlamaForCausalLM,
    tokenizer: CodeLlamaTokenizer,
    n_recs: int,
    period_stopping: PeriodStoppingCriteria,
    temperature: float = 0.2,
) -> SampleResult:
    period_stopping.set_num_periods(input_ids)
    stopping_list = StoppingCriteriaList([period_stopping])
    tactics: list[str] = []
    scores: list[float] = []
    num_tokens: list[int] = []
    for i in range(n_recs):
        output = model.generate(
            input_ids,
            temperature=temperature,
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
        tactic = tokenizer.decode(
            output_sequence[len(input_sequence) :], skip_special_tokens=True
        )
        score = get_sequence_score(
            input_sequence, output_sequence, output.scores, period_stopping
        )
        tactics.append(tactic)
        scores.append(score)
        num_tokens.append(output_length)
    return SampleResult(tactics, scores, num_tokens)


past_type = tuple[tuple[torch.LongTensor, torch.LongTensor]]


def __prepare_batches(
    input_ids: torch.LongTensor,
    beam_scores: torch.Tensor,
    past: Optional[past_type],
    batch_size: int,
) -> tuple[tuple[torch.LongTensor], tuple[torch.Tensor], list[Optional[past_type]],]:
    assert past is None  # Not implemented yet
    split_input_ids = torch.split(input_ids, batch_size)
    split_scores = torch.split(beam_scores, batch_size)
    if past:
        new_pasts: list[Optional[past_type]] = [tuple()] * len(split_scores)
        for (tup1, tup2), (tup3, tup4) in past:
            split_tup1 = torch.split(tup1, batch_size)
            split_tup2 = torch.split(tup2, batch_size)
            split_tup3 = torch.split(tup3, batch_size)
            split_tup4 = torch.split(tup4, batch_size)
            for i, (t1, t2, t3, t4) in enumerate(
                zip(split_tup1, split_tup2, split_tup3, split_tup4)
            ):
                new_pasts[i] += (((t1, t2), (t3, t4)),)
    else:
        new_pasts = [None] * len(split_scores)
    return split_input_ids, split_scores, new_pasts


class CompletedCandidate:
    def __init__(self, indices: torch.LongTensor, score: torch.Tensor) -> None:
        self.indices = indices
        self.score = score

    def __lt__(self, other: CompletedCandidate) -> bool:
        return float(self.score) < float(other.score)

    def __le__(self, other: CompletedCandidate) -> bool:
        return float(self.score) <= float(other.score)


def do_beam_sample(
    input_ids: torch.LongTensor,
    model: LlamaForCausalLM,
    tokenizer: CodeLlamaTokenizer,
    beam_width: int,
    n_recs: int,
    period_stopping: PeriodStoppingCriteria,
    batch_size: int = 2,
) -> SampleResult:
    past = None
    beam_scores = torch.zeros((input_ids.shape[0],), dtype=torch.float32).to("cuda")
    orig_input_length = int(input_ids.shape[1])

    completed_heap: list[CompletedCandidate] = []
    while True:
        batched_input_ids, batched_beam_scores, batched_pasts = __prepare_batches(
            input_ids,
            beam_scores,
            past,
            batch_size,
        )
        next_scores_list: list[torch.Tensor] = []
        next_input_id_list: list[torch.Tensor] = []

        print(len(batched_input_ids))
        print(input_ids.shape)
        for input_ids_batch, beam_score_batch, past_batch in zip(
            batched_input_ids,
            batched_beam_scores,
            batched_pasts,
        ):
            # print(
            #     tokenizer.batch_decode(
            #         input_ids_batch[:, orig_input_length:], skip_special_tokens=True
            #     )
            # )
            batch_inputs = model.prepare_inputs_for_generation(
                input_ids_batch, past_batch
            )
            output_batch = model(**batch_inputs)
            output_logits = output_batch[0]
            output_pasts = output_batch[1]
            next_token_logits = output_logits[:, -1, :]  # B x V
            next_token_scores = F.log_softmax(next_token_logits, dim=-1)  # B x V
            next_token_beam_scores = (
                next_token_scores + beam_score_batch[:, None]
            )  # B x V
            next_scores, next_tokens = torch.topk(
                next_token_beam_scores, beam_width, dim=-1, largest=True, sorted=True
            )
            batch_size, num_next_toks = next_tokens.shape
            input_batch_size, input_num_toks = input_ids_batch.shape
            prev_input_ids = (
                input_ids_batch[:, None, :]
                .expand(batch_size, num_next_toks, input_num_toks)
                .reshape(-1, input_num_toks)
            )
            next_input_ids = torch.cat(
                [prev_input_ids, next_tokens.reshape(-1, 1)], dim=1
            )
            flat_next_scores = next_scores.reshape(-1)
            assert next_input_ids.shape[0] == flat_next_scores.shape[0]
            next_scores_list.append(flat_next_scores)
            next_input_id_list.append(next_input_ids)

        all_next_scores = torch.cat(next_scores_list, dim=0)  # B x (B * n)
        all_next_inputs = torch.cat(next_input_id_list, dim=0)  # B x (B * n)

        ordered_next_scores, ordered_indices = torch.sort(
            all_next_scores, descending=True
        )
        ordered_next_token_ids = all_next_inputs[ordered_indices]

        next_batch_indices: list[int] = []
        for i, token_ids in enumerate(ordered_next_token_ids):
            if (
                token_ids[-1] == tokenizer.eos_token_id
                or token_ids[-1] in period_stopping.stop_tok_ids
            ):
                new_candidate = CompletedCandidate(token_ids, ordered_next_scores[i])
                heapq.heappush(completed_heap, new_candidate)
                if len(completed_heap) > n_recs:
                    heapq.heappop(completed_heap)
            elif (
                len(completed_heap) == 0
                or ordered_next_scores[i] > completed_heap[0].score
            ):
                next_batch_indices.append(i)

        if len(next_batch_indices) == 0:
            break

        indices_tensor = torch.tensor(next_batch_indices).to("cuda")
        input_ids = ordered_next_token_ids[indices_tensor]
        beam_scores = ordered_next_scores[indices_tensor]

    final_outputs: list[str] = []
    final_scores: list[float] = []
    final_num_toks: list[int] = []
    while len(completed_heap) > 0:
        candidate = completed_heap.pop()
        generated_ids = candidate.indices[orig_input_length:]
        output = tokenizer.decode(generated_ids, skip_special_tokens=True)
        final_outputs.append(output)
        final_scores.append(float(candidate.score))
        final_num_toks.append(len(generated_ids))

    return SampleResult(final_outputs, final_scores, final_num_toks)
