from __future__ import annotations
from typing import Any, Type, Optional

import sys, os
import pdb
import jsonlines

from data_management.dataset_file import (
    DatasetFile, FocusedStep, Proof, Sentence)
from model_deployment.premise_model_wrapper import LocalPremiseModelWrapper 


class LmExample:
    def __init__(self, input: str, output: str) -> None:
        assert type(input) == str
        assert type(output) == str
        self.input = input
        self.output = output

    def to_json(self) -> dict[str, str]:
        return {
            "input": self.input,
            "output": self.output,
        }

    @classmethod
    def json_from_dataset_file(cls, dataset_file: DatasetFile,
                               premise_model_wrapper: Optional[LocalPremiseModelWrapper]) -> list[dict[str, str]]:
        return [example.to_json() for example in cls.from_dataset_file(dataset_file, premise_model_wrapper)]

    @classmethod
    def from_dataset_file(cls, dataset_file: DatasetFile,
                          premise_model_wrapper: Optional[LocalPremiseModelWrapper]) -> list[LmExample]:
        raise NotImplementedError

    @classmethod
    def from_json(cls, json_data: Any) -> LmExample:
        input = json_data["input"]
        output = json_data["output"]
        return cls(input, output)

    @staticmethod
    def get_alias() -> str:
        raise NotImplementedError


class BasicLmExample(LmExample):
    def __init__(self, input: str, output: str) -> None:
        super(BasicLmExample, self).__init__(input, output)

    @classmethod
    def example_from_step(cls, step: FocusedStep, proof: Proof) -> BasicLmExample:
        goal_strings: list[str] = []
        for goal in step.goals:
            goal_strings.append(goal.to_string())
        partial_proof_string = proof.proof_prefix_to_string(step)
        final_goal_string = "<GOAL-SEP>".join(goal_strings)
        input = f"{partial_proof_string}<THM-SEP>{final_goal_string}"
        output = step.step.text
        return cls(input, output)

    @classmethod
    def from_dataset_file(cls, dataset_file: DatasetFile,
                          premise_model_wrapper: Optional[LocalPremiseModelWrapper]) -> list[LmExample]:
        basic_lm_examples: list[LmExample] = []
        for proof in dataset_file.proofs:
            for step in proof.steps:
                basic_lm_examples.append(cls.example_from_step(step, proof))
        return basic_lm_examples

    @staticmethod
    def get_alias() -> str:
        return "basic"



class PremiseLmExample(LmExample):
    MAX_N_EXAMPLES = 100

    def __init__(self, input: str, output: str) -> None:
        super(PremiseLmExample, self).__init__(input, output)

    
    @staticmethod
    def get_predicted_logical_path(premise_file_path: str, cur_file_path: str) -> str:
        """Helpful: https://coq.inria.fr/refman/practical-tools/utilities.html?highlight=imports"""
        coq_lib_str = os.path.join("lib", "coq", "theories") + "/"
        if coq_lib_str in premise_file_path:
            coq_lib_str_idx = premise_file_path.index(coq_lib_str) 
            start_idx = coq_lib_str_idx + len(coq_lib_str) 
            log_path = premise_file_path[start_idx:].replace("/", ".").rstrip(".v")
            return f"Coq.{log_path}"

        coq_contrib_str = os.path.join("lib", "user-contrib") + "/"
        if coq_contrib_str in premise_file_path:
            coq_contrib_str_idx = premise_file_path.index(coq_contrib_str)
            start_idx = coq_contrib_str_idx + len(coq_contrib_str)
            log_path = premise_file_path[start_idx:].replace("/", ".").rstrip(".v")
            return log_path

        prefix = ""
        first_tok = cur_file_path[0]
        split_toks = cur_file_path[1:].split("/")
        split_toks[0] = first_tok + split_toks[0]
        i = 0
        proposed_prefix = os.path.join(prefix, split_toks[i])
        raise NotImplementedError
        while premise_file_path.startswith(proposed_prefix) and i < len(split_toks):
            prefix = proposed_prefix 
            i += 1
            proposed_prefix = os.path.join(prefix, split_toks[i])
            #### TODOTODOTODOTODO
        


    @classmethod
    def __get_premise_str(cls, step: FocusedStep, 
                          proof: Proof, 
                          dset_obj: DatasetFile,
                          premise_model_wrapper: LocalPremiseModelWrapper) -> str:
        filtered_result = premise_model_wrapper.premise_filter.get_pos_and_avail_premises(
            step, proof, dset_obj)
        ranked_premises = premise_model_wrapper.get_ranked_premise_generator(
            step, proof, filtered_result.avail_premises)
        top_premises: list[Sentence] = []
        for premise in ranked_premises:
            if len(top_premises) >= cls.MAX_N_EXAMPLES:
                break
            top_premises.append(premise)

        premise_strs: list[str] = []
        for i, premise in enumerate(top_premises):
            premise_strs.append(f"Premise {i + 1}: {premise.text}")
        
        premise_strs.reverse()
        return "\n".join(premise_strs)


    @classmethod
    def example_from_step(cls, step: FocusedStep, 
                            proof: Proof, 
                            dset_obj: DatasetFile,
                            premise_model_wrapper: LocalPremiseModelWrapper) -> PremiseLmExample:
        basic_example = BasicLmExample.example_from_step(step, proof)
        premise_str = cls.__get_premise_str(step, proof, dset_obj, premise_model_wrapper)
        example_input = f"{premise_str}<PREM-SEP>{basic_example.input}"
        example_output = basic_example.output
        return cls(example_input, example_output) 

    
    @classmethod
    def from_dataset_file(cls, dataset_file: DatasetFile, 
                          premise_model_wrapper: Optional[LocalPremiseModelWrapper]) -> list[LmExample]:
        assert premise_model_wrapper is not None
        premise_examples: list[LmExample] = []
        for proof in dataset_file.proofs:
            for step in proof.steps:
                premise_example = cls.example_from_step(
                    step, proof, dataset_file, premise_model_wrapper)
                premise_examples.append(premise_example)
        return premise_examples


    @staticmethod
    def get_alias() -> str:
        return "premise"

class BaseCodeLLamaLmExample(LmExample):
    def __init__(self, input: str, output: str) -> None:
        super(BaseCodeLLamaLmExample, self).__init__(input, output)
    
    @classmethod
    def example_from_step(cls, step: FocusedStep, proof: Proof) -> BaseCodeLLamaLmExample:
        goal_strings: list[str] = []
        for i, goal in enumerate(step.goals):
            goal_strings.append(f"Goal {i + 1}:\n{goal.to_string()}")
        partial_proof_string = proof.proof_prefix_to_string(step)
        final_goal_string = "\n\n".join(goal_strings)
        input = f"{final_goal_string}\n\n{partial_proof_string}"
        output = step.step.text
        return cls(input, output)

    @classmethod
    def from_dataset_file(cls, dataset_file: DatasetFile, premise_model_wrapper: LocalPremiseModelWrapper | None) -> list[LmExample]:
        code_llama_examples: list[LmExample] = []
        for proof in dataset_file.proofs:
            for step in proof.steps:
                code_llama_examples.append(cls.example_from_step(step, proof))
        return code_llama_examples 

    @staticmethod
    def get_alias() -> str:
        return "codellama-base"



class GPT4BasicLmExample(LmExample):
    SCRIPT_TAG = "<PSCRIPT>"
    STATE_TAG = "<STATE>"
    SYS_MSG = ("You are given a partial coq proof following "
               f"the {SCRIPT_TAG} tag. You are given the proof "
               f"state of the partial proof following the {STATE_TAG} "
               "tag. You respond with the next coq command to use "
               "in order to eventually complete the proof. ") 
    def __init__(self, input: str, output: str) -> None:
        super(GPT4BasicLmExample, self).__init__(input, output)


    @classmethod
    def example_from_step(cls, step: FocusedStep, proof: Proof) -> GPT4BasicLmExample:
        goal_strings: list[str] = []
        for i, goal in enumerate(step.goals):
            goal_strings.append(f"Goal {i + 1}\n{goal.to_string()}")
        partial_proof_string = proof.proof_prefix_to_string(step)
        final_goal_string = "\n".join(goal_strings)
        input = f"{cls.SCRIPT_TAG}\n{partial_proof_string}\n{cls.STATE_TAG}\n{final_goal_string}"
        output = step.step.text
        return cls(input, output)


    @classmethod
    def from_dataset_file(cls, dataset_file: DatasetFile,
                          premise_model_wrapper: Optional[LocalPremiseModelWrapper]) -> list[LmExample]:
        gpt4_examples: list[LmExample] = []
        for proof in dataset_file.proofs:
            for step in proof.steps:
                gpt4_examples.append(cls.example_from_step(step, proof))
        return gpt4_examples


    @staticmethod
    def get_alias() -> str:
        return "gpt4-basic"


LMEXAMPLE_ALIASES: dict[str, Type[LmExample]] = {
    BasicLmExample.get_alias(): BasicLmExample, 
    GPT4BasicLmExample.get_alias(): GPT4BasicLmExample,
    PremiseLmExample.get_alias(): PremiseLmExample,
    BaseCodeLLamaLmExample.get_alias(): BaseCodeLLamaLmExample,
}


if __name__ == "__main__":
    TEST_PATH = "/Users/kylethompson/UCSD/llm-difference-descriptions/coq-lsp-mining/res/"
    all_examples: list[LmExample] = []
    for dirname in os.listdir(TEST_PATH):
        absolute_dirname = os.path.join(TEST_PATH, dirname)
        obj = DatasetFile.from_directory(absolute_dirname)
        premise_wrapper: Optional[LocalPremiseModelWrapper] = None
        examples = BasicLmExample.from_dataset_file(obj, premise_wrapper)
        all_examples.extend(examples)

    with jsonlines.open("test_examples.jsonl", "w") as fout:
        fout.write_all([e.to_json() for e in all_examples])

                

