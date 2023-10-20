from __future__ import annotations
from typing import Any, Optional
from types import TracebackType

import pickle
import time
import traceback
import sys, os
import shutil
from enum import Enum
import pdb
import jsonlines

from data_management.dataset_file import DatasetFile, STEPS_NAME, FILE_CONTEXT_NAME
from data_management.create_lm_dataset import LmExampleConfig
from data_management.get_counts import remove_comments
from tactic_gen.lm_example import LmExample
from model_deployment.goal_comparer import (
    ParsedObligations,
    ParsedObligation,
    ParsedHyp,
)


from coqlspclient.coq_structs import ProofTerm, Term, Step, RangedSpan
from coqlspclient.coq_lsp_structs import Goal, GoalAnswer
from coqlspclient.proof_file import ProofFile
from coqlspclient.coq_file import CoqFile


class TacticResult(Enum):
    COMPLETE = 1
    VALID = 2
    INVALID = 3


class ProofCheckResult:
    def __init__(
        self,
        tactic_result: TacticResult,
        valid_steps: list[str],
        current_goals: Optional[GoalAnswer],
        parsed_current_goals: Optional[ParsedObligations],
    ) -> None:
        assert type(tactic_result) == TacticResult
        assert type(valid_steps) == list
        assert all([type(s) == str for s in valid_steps])
        self.tactic_result = tactic_result
        self.valid_steps = valid_steps
        self.current_goals = current_goals
        self.parsed_current_goals = parsed_current_goals

    @classmethod
    def get_invalid(cls) -> ProofCheckResult:
        current_goals = None
        parsed_current_goals = None
        return cls(TacticResult.INVALID, [], current_goals, parsed_current_goals)


def proc_file_path(file_path: str) -> str:
    if file_path.startswith("/home"):
        return "/".join(file_path.split("/")[3:])
    return file_path


def get_context(context: list[Term]) -> list[dict[str, Any]]:
    res = []
    for term in context:
        res.append(
            {
                "text": term.text,
                "file_path": proc_file_path(term.file_path),
                "module": term.module,
                "type": str(term.type),
                "line": term.ast.range.start.line,
            }
        )
    return res


def get_prefix_from_str(file_str: str, search_token: str) -> Optional[str]:
    token_idx = file_str.find(search_token)
    if token_idx == -1:
        return None
    return file_str[:token_idx].strip()


def get_file_prefix(filename: str, search_token: str) -> Optional[str]:
    with open(filename, "r") as fin:
        file_contents = fin.read()
    return get_prefix_from_str(file_contents, search_token)


def get_fresh_path(dirname: str, fresh_base: str) -> str:
    name = fresh_base
    while os.path.exists(os.path.join(dirname, name)):
        name = "_" + name
    return os.path.join(dirname, name)


def get_last_proof_data_points(proof: ProofTerm) -> Any:
    data_points = []
    for i, step in enumerate(proof.steps):
        assert step.goals.goals is not None
        goals = list(map(lambda goal: repr(goal), step.goals.goals.goals))
        next_steps: list[dict[str, Any]] = []
        data_point = {
            "term": {
                "text": proof.text,
                "file_path": proc_file_path(proof.file_path),
                "module": proof.module,
                "type": str(proof.type),
                "line": proof.ast.range.start.line,
                "context": get_context(proof.context),
            },
            "step": {"text": step.text, "context": get_context(step.context)},
            "n_step": i + 1,
            "goals": goals,
            "next_steps": next_steps,
        }
        for next_step in proof.steps[i + 1 :]:
            next_steps.append(
                {"text": next_step.text, "context": get_context(next_step.context)}
            )
        data_points.append(data_point)
    return data_points


SEARCH_TOKEN = "<prove>"


def set_hidden_files(
    hidden_file_path: str, aux_hidden_file_path: str, prefix: str
) -> None:
    with open(hidden_file_path, "w") as fout:
        fout.write(f"{prefix}\nAdmitted.")
    with open(aux_hidden_file_path, "w") as fout:
        fout.write(f"{prefix}")


def initialize_hidden_files(orig_file_path: str) -> tuple[str, str]:
    """
    Find a fresh file path, and copy the contents of the original
    file to the fresh file up to the <prove> token. Replace the
    <prove> token with `Admitted`.
    """
    file_dirname = os.path.dirname(orig_file_path)
    file_basename = os.path.basename(orig_file_path)
    fresh_file_path = get_fresh_path(file_dirname, file_basename)
    fresh_aux_file_path = get_fresh_path(file_dirname, f"aux_{file_basename}")
    file_prefix = get_file_prefix(orig_file_path, SEARCH_TOKEN)
    if file_prefix is None:
        raise ValueError(f"Could not find search token {SEARCH_TOKEN}")
    set_hidden_files(fresh_file_path, fresh_aux_file_path, file_prefix)
    return fresh_file_path, fresh_aux_file_path


def hidden_files_from_prefix(orig_file_path: str, file_prefix: str) -> tuple[str, str]:
    file_dirname = os.path.dirname(orig_file_path)
    file_basename = os.path.basename(orig_file_path)
    fresh_file_path = get_fresh_path(file_dirname, file_basename)
    fresh_aux_file_path = get_fresh_path(file_dirname, f"aux_{file_basename}")
    prefix_no_tok = get_prefix_from_str(file_prefix, SEARCH_TOKEN)
    if prefix_no_tok is None:
        raise ValueError(f"Could not find search token {SEARCH_TOKEN}")
    set_hidden_files(fresh_file_path, fresh_aux_file_path, prefix_no_tok)
    return fresh_file_path, fresh_aux_file_path


class ProofManager:
    TIMEOUT = 60
    LAST_TACTIC_IDX = -3  # -1 is garbage. -2 is "Admitted.". -3 is last tactic.

    def __init__(
        self,
        file_path: str,
        proof_file: ProofFile,
        aux_file_path: str,
        lm_example_config: LmExampleConfig,
    ) -> None:
        file_dir = os.path.dirname(file_path)
        self.file_path = file_path
        self.example_type = lm_example_config.format_type
        self.premise_wrapper = lm_example_config.premise_wrapper
        self.__search_dir_path = get_fresh_path(file_dir, ".proof-search")
        self.aux_file_path = aux_file_path
        with open(self.aux_file_path, "r") as fin:
            self.file_prefix = fin.read()

        self.proof_file = proof_file
        self.base_num_steps = len(proof_file.steps)
        self.proof_start_idx = self.__get_last_tactic_idx() + 1  # No tactics yet!
        self.last_proof_attempted: str | None = None

    def __get_last_tactic_idx(self) -> int:
        return len(self.proof_file.steps) + self.LAST_TACTIC_IDX

    def __is_proof_prefix(self, steps1: list[str], steps2: list[str]) -> bool:
        if len(steps1) > len(steps2):
            return False
        for i, step in enumerate(steps1):
            if step != steps2[i]:
                return False
        return True

    def __get_current_partial_proof(self) -> list[str]:
        stop_idx = self.LAST_TACTIC_IDX + 1  # Include last tactic
        return [s.text for s in self.proof_file.steps[self.proof_start_idx : stop_idx]]

    def set_proof_file(
        self,
        valid_steps: list[str],
        target_combined_proof: str,
        partial_proof_suffix: str,
    ) -> None:
        assert len(self.proof_file.steps) >= self.base_num_steps
        current_partial_proof = self.__get_current_partial_proof()
        while not self.__is_proof_prefix(current_partial_proof, valid_steps):
            to_remove_index = self.__get_last_tactic_idx()
            self.proof_file.delete_step(to_remove_index)
            current_partial_proof = self.__get_current_partial_proof()
        prefix_len = len(current_partial_proof)
        remaining_current_proof = valid_steps[prefix_len:]
        for step in remaining_current_proof:
            last_tactic_idx = self.__get_last_tactic_idx()
            self.proof_file.add_step(step, last_tactic_idx)
        final_partial_proof = self.__get_current_partial_proof()
        assert (
            target_combined_proof == "".join(final_partial_proof) + partial_proof_suffix
        )

    def __update_aux_file(self, partial_proof: str) -> None:
        with open(self.aux_file_path, "w") as fout:
            fout.write(f"{self.file_prefix}{partial_proof}")

    def __get_valid_steps(self, valid_coq_file: CoqFile) -> list[str]:
        assert valid_coq_file.is_valid
        suffix_steps = valid_coq_file.steps[self.proof_start_idx : -1]
        nonempty_steps: list[str] = []
        for s in suffix_steps:
            if len(s.text.strip()) > 0:
                nonempty_steps.append(s.text)
        return nonempty_steps

    def __get_goal_strs(self, current_goals: GoalAnswer) -> list[str]:
        assert current_goals.goals is not None
        collapsed_stack: list[Goal] = []
        for stack_goals1, stack_goals2 in current_goals.goals.stack:
            collapsed_stack.extend(stack_goals1)
            collapsed_stack.extend(stack_goals2)
        real_goals = (
            current_goals.goals.goals + collapsed_stack + current_goals.goals.shelf
        )
        final_strings: list[str] = []
        for i, goal in enumerate(real_goals):
            for j, hyp in enumerate(goal.hyps):
                final_strings.append(f"Definition g_{i}_h_{j} := ({hyp.ty}).")
            final_strings.append(f"Definition g_{i} := ({goal.ty}).")
        return final_strings

    def __extract_body_from_def_ast(self, def_ast: Any) -> Any:
        def_expr = def_ast["v"]["expr"][1]
        try:
            assert def_expr[0] == "VernacDefinition"
        except AssertionError:
            pdb.set_trace()
        return def_expr[3]

    def __read_definition(
        self, coq_file: CoqFile, num_definitions: int, num_read: int
    ) -> tuple[Any, int]:
        num_steps = len(coq_file.steps)
        read_idx = num_steps - num_definitions - 1 + num_read
        whole_def_ast = coq_file.steps[read_idx].ast.span
        ast_def_body = self.__extract_body_from_def_ast(whole_def_ast)
        return ast_def_body, num_read + 1

    def get_parsed_goals(
        self, partial_proof: str, current_goals: GoalAnswer
    ) -> ParsedObligations:
        assert current_goals.goals is not None
        goal_as_definitions = self.__get_goal_strs(current_goals)
        goal_str = "\n\n".join(goal_as_definitions)
        to_write = f"{partial_proof}\n\n{goal_str}"
        self.__update_aux_file(to_write)
        num_read = 0
        num_definitions = len(goal_as_definitions)
        parsed_goals: list[ParsedObligation] = []
        with CoqFile(self.aux_file_path) as coq_file:
            for goal in current_goals.goals.goals:
                parsed_hyps: list[ParsedHyp] = []
                for hyp in goal.hyps:
                    hyp_ast, num_read = self.__read_definition(
                        coq_file, num_definitions, num_read
                    )
                    parsed_hyp = ParsedHyp(hyp.names, hyp_ast)
                    parsed_hyps.append(parsed_hyp)
                goal_ast, num_read = self.__read_definition(
                    coq_file, num_definitions, num_read
                )
                parsed_goal = ParsedObligation(parsed_hyps, goal_ast)
                parsed_goals.append(parsed_goal)
        return ParsedObligations(parsed_goals)

    def check_proof(
        self, partial_proof: str, prev_valid_steps: list[str]
    ) -> ProofCheckResult:
        if (
            ("Admitted." in partial_proof)
            or ("admit." in partial_proof)
            or ("Abort." in partial_proof)
        ):
            return ProofCheckResult.get_invalid()
        self.__update_aux_file(partial_proof)
        with CoqFile(self.aux_file_path) as coq_file:
            if not coq_file.is_valid:
                return ProofCheckResult.get_invalid()
            coq_file.run()
            valid_steps = self.__get_valid_steps(coq_file)
            assert self.__is_proof_prefix(prev_valid_steps, valid_steps)
            new_valid_steps = valid_steps[len(prev_valid_steps) :]
            # might not have to compute this here
            current_goals = coq_file.current_goals()
            if not coq_file.in_proof:
                parsed_obligations = None
                return ProofCheckResult(
                    TacticResult.COMPLETE,
                    new_valid_steps,
                    current_goals,
                    parsed_obligations,
                )

        parsed_obligations = self.get_parsed_goals(partial_proof, current_goals)
        return ProofCheckResult(
            TacticResult.VALID, new_valid_steps, current_goals, parsed_obligations
        )

    def get_example(
        self, valid_steps: list[str], target_combined_steps: str
    ) -> LmExample:
        combined_valid_step_str = "".join(valid_steps)
        try:
            assert len(target_combined_steps) >= len(combined_valid_step_str)
            assert target_combined_steps.startswith(combined_valid_step_str)
        except AssertionError:
            pdb.set_trace()

        partial_proof_suffix = target_combined_steps[len(combined_valid_step_str) :]
        dataset_obj = self.get_dataset_file(
            valid_steps, target_combined_steps, partial_proof_suffix
        )
        examples = self.example_type.from_dataset_file(
            dataset_obj, self.premise_wrapper, partial_proof_suffix
        )
        example = examples[-1]
        return example

    def get_dataset_file(
        self,
        valid_steps: list[str],
        target_combined_steps: str,
        partial_proof_suffix: str,
    ) -> DatasetFile:
        start = time.time_ns()
        self.set_proof_file(valid_steps, target_combined_steps, partial_proof_suffix)
        end = time.time_ns()
        print("ProofFile Update Time:", (end - start) / 1e9)
        self.__update_search_dir(self.proof_file)
        dataset_obj = DatasetFile.from_directory(self.__search_dir_path)
        return dataset_obj

    def __update_search_dir(self, proof_file: ProofFile) -> None:
        last_proof = proof_file.proofs[-1]
        last_proof_data = get_last_proof_data_points(last_proof)
        context_list = list(proof_file.context.terms.values())
        context_data = get_context(context_list)
        steps_loc = os.path.join(self.__search_dir_path, STEPS_NAME)
        context_loc = os.path.join(self.__search_dir_path, FILE_CONTEXT_NAME)
        if not os.path.exists(self.__search_dir_path):
            os.makedirs(self.__search_dir_path)
        if os.path.exists(steps_loc):
            os.remove(steps_loc)
        if os.path.exists(context_loc):
            os.remove(context_loc)

        with jsonlines.open(steps_loc, "w") as fout:
            fout.write_all(last_proof_data)
        with jsonlines.open(context_loc, "w") as fout:
            fout.write_all(
                [
                    {
                        "file": proc_file_path(last_proof.file_path),
                        "context": context_data,
                    }
                ]
            )

    def __enter__(self) -> ProofManager:
        return self

    def __exit__(
        self,
        exc_type: type[BaseException],
        exc_value: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        self.close()

    def close(self) -> None:
        if os.path.exists(self.file_path):
            # os.remove(self.file_path)
            pass
        if os.path.exists(self.aux_file_path):
            # os.remove(self.aux_file_path)
            pass
        if os.path.exists(self.__search_dir_path):
            shutil.rmtree(self.__search_dir_path)
