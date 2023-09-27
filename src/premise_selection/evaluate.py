
from typing import Type, Iterable

import sys, os
import argparse

import torch
from transformers import ByT5Tokenizer, T5EncoderModel


from data_management.split_raw_data import SPLITS
from data_management.split_raw_data import data_shape_expected
from data_management.dataset_file import DatasetFile, Sentence
from premise_selection.model import PremiseRetriever 
from premise_selection.premise_formatter import PremiseFormat, ContextFormat
from premise_selection.datamodule import tokenize_strings 


class EvalResult:
    def __init__(self, num_premises: int, 
                 num_recs_required: int) -> None:
        """
        num_recs_required: number of recommendations required
          before all ground truth recommendations were recommended
        """
        self.num_premises = num_premises
        self.num_recs_required = num_recs_required


class Evaluator:
    def __init__(self, model_loc: str,
                 partitioned_data_loc: str,
                 split: str,
                 premise_format: Type[PremiseFormat],
                 context_format: Type[ContextFormat]) -> None:
        assert type(model_loc) == str
        assert type(partitioned_data_loc) == str
        assert type(split) == str
        assert split in SPLITS
        split_loc = os.path.join(partitioned_data_loc, split)
        assert data_shape_expected(split_loc)
        self.model_loc = model_loc
        self.model = self.__load_model()
        self.tokenizer = self.__load_tokenizer()
        self.max_seq_len = self.__get_max_seq_len()
        self.partitioned_data_loc = partitioned_data_loc
        self.split = split
        self.embedding_cache: dict[str, torch.Tensor] = {}
        self.split_loc = os.path.join(partitioned_data_loc, split)
        self.premise_format = premise_format
        self.context_format = context_format


    def __get_max_seq_len(self) -> int:
        pass

    def __load_model(self) -> PremiseRetriever:
        pass

    def __load_tokenizer(self) -> ByT5Tokenizer:
        pass 

    
    def __get_embedding(self, to_embed: str) -> torch.Tensor:
        if to_embed in self.embedding_cache:
            return self.embedding_cache[to_embed]
        tokens = tokenize_strings(
            self.tokenizer, [to_embed], self.max_seq_len) 
        input_ids = tokens.input_ids 
        input_masks = tokens.attention_mask
        encoding = self.model._encode(input_ids, input_masks) # shape should be 1 x h_dim
        assert encoding.shape[0] == 1
        self.embedding_cache[to_embed] = encoding
        return encoding 


    def __get_ranked_premises(self, context: str, premises: list[Sentence]) -> Iterable[Sentence]:
        context_embedding = self.__get_embedding(context) 
        prem_embeddings: list[torch.Tensor] = []
        for prem in premises:
            formatted_prem = self.premise_format.format(prem)
            prem_embeddings.append(self.__get_embedding(formatted_prem)) 
        all_prem_embeddings = torch.cat(prem_embeddings)
        scores = torch.mm(context_embedding, all_prem_embeddings)
        flat_scores = scores.squeeze()
        assert flat_scores.ndim == 1
        sentence_order = list[torch.argsort(flat_scores, descending=True)]
        for idx in sentence_order:
            yield premises[idx]


    def run_evaluation(self) -> tuple[int, list[EvalResult]]:
        """Note that |eval_results| = # steps requiring at least one premise."""
        num_steps = 0
        eval_results: list[EvalResult] = []
        for raw_dataset_file in os.listdir(self.split_loc):
            parsed_dataset_file = DatasetFile.from_directory(raw_dataset_file)
            for proof in parsed_dataset_file.proofs:
                for step in proof.steps:
                    num_steps += 1
                    num_premises = len(step.step.context)
                    if num_premises == 0:
                        continue
                    formatted_context = self.context_format.format(step, proof)
                    premises_to_cover = step.step.context.copy()
                    premises_available = parsed_dataset_file.get_premises_before(proof)
                    ranked_premises_generator = self.__get_ranked_premises(
                        formatted_context, premises_available)
                    for i, premise_rec in enumerate(ranked_premises_generator):
                        try:
                            premises_to_cover.remove(premise_rec)
                            if len(premises_to_cover) == 0:
                                break
                        except ValueError:
                            continue
                    assert len(premises_to_cover) == 0
                    num_recs_required = i + 1
                    eval_results.append(EvalResult(num_premises, num_recs_required))
        return num_steps, eval_results



if __name__=="__main__":
    parser = argparse.ArgumentParser(
        description="Conduct an evaluation of a premise selection model.")
    parser.add_argument("model_loc",
                        help="Location of the model to evaluate.")
    parser.add_argument("partitioned_data_loc",
                        help="Location of partitioned raw data to evaluate.")
    parser.add_argument("split",
                        help=f"Partition of data to evaluate. One of {SPLITS}")
    args = parser.parse_args(sys.argv[1:])

            
                    