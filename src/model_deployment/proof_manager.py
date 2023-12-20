from __future__ import annotations
from typing import Any, Optional
from types import TracebackType

import sys, os
from enum import Enum
import ipdb

from typeguard import typechecked

from util.util import get_fresh_path
from data_management.dataset_file import (
    DatasetFile,
    FileContext,
)
from data_management.splits import Split, FileInfo

from tactic_gen.lm_example import LmExample, LmFormatter
from model_deployment.goal_comparer import (
    ParsedObligations,
    ParsedObligation,
    ParsedHyp,
    extract_body_from_step,
)
from util.util import get_basic_logger

from coqpyt.coq.changes import CoqAddStep, CoqDeleteStep
from coqpyt.coq.structs import ProofTerm, Term
from coqpyt.coq.lsp.structs import Goal, GoalAnswer
from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.exceptions import InvalidChangeException

_logger = get_basic_logger(__name__)


class TacticResult(Enum):
    COMPLETE = 1
    VALID = 2
    INVALID = 3


@typechecked
class ProofCheckResult:
    def __init__(
        self,
        tactic_result: TacticResult,
        attempted_steps: list[str],
        current_goals: Optional[GoalAnswer],
        parsed_current_goals: Optional[ParsedObligations],
        new_dataset_file: Optional[DatasetFile],
    ) -> None:
        self.tactic_result = tactic_result
        self.attempted_steps = attempted_steps
        self.current_goals = current_goals
        self.parsed_current_goals = parsed_current_goals
        self.dataset_file = new_dataset_file

    @classmethod
    def get_invalid(cls) -> ProofCheckResult:
        current_goals = None
        parsed_current_goals = None
        new_dataset_file = None
        return cls(
            TacticResult.INVALID,
            [],
            current_goals,
            parsed_current_goals,
            new_dataset_file,
        )


def proc_file_path(file_path: str) -> str:
    if file_path.startswith("/home"):
        return "/".join(file_path.split("/")[3:])
    return file_path


def get_context(context: list[Term]) -> list[dict[str, Any]]:
    res: list[dict[str, Any]] = []
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


def get_last_proof_data_points(proof: ProofTerm) -> Any:
    data_points: list[dict[str, Any]] = []
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


@typechecked
class ProofManager:
    TIMEOUT = 60

    def __init__(
        self,
        file_path: str,
        proof_file: ProofFile,
        proof_point: int,
        lm_formatter: LmFormatter,
        file_info: FileInfo,
        split: Split,
        data_loc: str,
    ) -> None:
        file_dir = os.path.dirname(file_path)
        file_basename = os.path.basename(file_path)
        self.file_path = file_path
        self.lm_formatter = lm_formatter
        self.aux_file_path = get_fresh_path(file_dir, f"aux_{file_basename}")

        self.proof_file = proof_file
        self.proof_point = proof_point

        self.file_info = file_info
        self.split = split
        self.data_loc = data_loc

        self.file_prefix = self.__get_file_prefix()
        self.__proof_stored_steps = self.__replace_proof_with_admitted_stub()

    def __get_file_prefix(self) -> str:
        return "".join(
            [s.text for s in self.proof_file.steps[: (self.proof_point + 1)]]
        )

    def __go_through_point(self, point: int) -> None:
        while self.proof_file.steps_taken < point + 1:
            self.proof_file.exec(1)
        while point + 1 < self.proof_file.steps_taken:
            self.proof_file.exec(-1)

    def __go_to_point(self, point: int) -> None:
        while self.proof_file.steps_taken < point:
            self.proof_file.exec(1)
        while point < self.proof_file.steps_taken:
            self.proof_file.exec(-1)

    def __get_whole_proof_delete_steps(self) -> tuple[list[int], list[str]]:
        delete_indices: list[int] = []
        delete_strs: list[str] = []
        self.__go_through_point(self.proof_point)
        assert self.proof_file.in_proof
        while self.proof_file.in_proof and self.proof_file.steps_taken < len(
            self.proof_file.steps
        ):
            delete_idx = self.proof_file.steps_taken
            delete_strs.append(self.proof_file.steps[delete_idx].text)
            delete_indices.append(delete_idx)
            self.proof_file.exec(1)
        return delete_indices, delete_strs

    def __replace_proof_with_admitted_stub(self) -> list[str]:
        delete_indices, delete_strs = self.__get_whole_proof_delete_steps()
        delete_commands = [CoqDeleteStep(i) for i in reversed(delete_indices)]
        self.__go_through_point(self.proof_point)
        add_commands = [CoqAddStep("\nAdmitted.", self.proof_file.steps_taken - 1)]
        self.proof_file.change_steps(delete_commands + add_commands)
        return delete_strs

    def __restore_proof_file(self) -> None:
        delete_indices, _ = self.__get_whole_proof_delete_steps()
        delete_steps = [CoqDeleteStep(i) for i in reversed(delete_indices)]
        add_steps = [
            CoqAddStep(s, self.proof_point + i)
            for i, s in enumerate(self.__proof_stored_steps)
        ]
        self.proof_file.change_steps(delete_steps + add_steps)

    def __is_proof_prefix(self, steps1: list[str], steps2: list[str]) -> bool:
        if len(steps1) > len(steps2):
            return False
        for i, step in enumerate(steps1):
            if step != steps2[i]:
                return False
        return True

    def __get_current_partial_proof(self) -> list[str]:
        start_idx = self.proof_point + 1
        stop_idx = self.proof_file.steps_taken
        return [s.text for s in self.proof_file.steps[start_idx:stop_idx]]

    def __add_step_to_proof_file(self, step: str) -> None:
        assert self.proof_file.in_proof
        self.proof_file.add_step(self.proof_file.steps_taken - 1, step)
        self.proof_file.exec(1)
        assert self.proof_file.in_proof

    def __delete_step_from_proof_file(self) -> None:
        assert self.proof_file.in_proof
        self.proof_file.exec(-1)
        self.proof_file.delete_step(self.proof_file.steps_taken)
        assert self.proof_file.in_proof

    def set_proof_file(
        self,
        steps: list[str],
    ) -> None:
        current_partial_proof = self.__get_current_partial_proof()
        prefix_len = 0
        while (
            prefix_len < len(current_partial_proof)
            and prefix_len < len(steps)
            and current_partial_proof[prefix_len] == steps[prefix_len]
        ):
            prefix_len += 1

        num_steps_to_delete = len(current_partial_proof) - prefix_len
        self.__go_to_point(self.proof_point)
        delete_steps = [
            CoqDeleteStep(self.proof_point + prefix_len + i)
            for i in range(num_steps_to_delete, 0, -1)
        ]
        add_steps = [
            CoqAddStep(s, self.proof_point + prefix_len + i)
            for i, s in enumerate(steps[prefix_len:])
        ]
        self.proof_file.change_steps(delete_steps + add_steps)
        self.__go_through_point(self.proof_point + len(steps))
        assert "Admitted." in self.proof_file.steps[self.proof_file.steps_taken].text
        # while not self.__is_proof_prefix(current_partial_proof, steps):
        #     self.__delete_step_from_proof_file()
        #     current_partial_proof = self.__get_current_partial_proof()
        # prefix_len = len(current_partial_proof)
        # remaining_current_proof = steps[prefix_len:]
        # for step in remaining_current_proof:
        #     self.__add_step_to_proof_file(step)
        # _logger.debug("".join(self.__get_current_partial_proof()))
        # _logger.debug(f"Can close proof: {self.proof_file.can_close_proof}")

    def __update_aux_file(self, partial_proof: str) -> None:
        with open(self.aux_file_path, "w") as fout:
            fout.write(f"{self.file_prefix}{partial_proof}")

    def __get_all_goals(self, current_goals: GoalAnswer) -> list[Goal]:
        assert current_goals.goals is not None
        collapsed_stack: list[Goal] = []
        for stack_goals1, stack_goals2 in current_goals.goals.stack:
            collapsed_stack.extend(stack_goals1)
            collapsed_stack.extend(stack_goals2)
        return current_goals.goals.goals + collapsed_stack + current_goals.goals.shelf

    def __get_goal_strs(self, current_goals: GoalAnswer) -> list[str]:
        all_goals = self.__get_all_goals(current_goals)
        final_strings: list[str] = []
        for i, goal in enumerate(all_goals):
            for j, hyp in enumerate(goal.hyps):
                final_strings.append(f"Definition g_{i}_h_{j} := ({hyp.ty}).")
            final_strings.append(f"Definition g_{i} := ({goal.ty}).")
        return final_strings

    def __read_definition(
        self, coq_file: CoqFile, num_definitions: int, num_read: int
    ) -> tuple[Any, str, int]:
        num_steps = len(coq_file.steps)
        read_idx = num_steps - num_definitions + num_read
        def_text = coq_file.steps[read_idx].text
        ast_def_body = extract_body_from_step(coq_file.steps[read_idx])
        return ast_def_body, def_text, num_read + 1

    def get_parsed_goals(
        self, partial_proof: str, current_goals: GoalAnswer
    ) -> ParsedObligations:
        assert current_goals.goals is not None
        all_goals = self.__get_all_goals(current_goals)
        _logger.debug(f"Num goals: {len(all_goals)}")
        goal_as_definitions = self.__get_goal_strs(current_goals)
        goal_str = "\n\n".join(goal_as_definitions)
        to_write = f"{partial_proof}\n\n{goal_str}"
        self.__update_aux_file(to_write)
        num_read = 0
        num_definitions = len(goal_as_definitions)
        parsed_goals: list[ParsedObligation] = []
        with CoqFile(self.aux_file_path) as coq_file:
            for goal in all_goals:
                parsed_hyps: list[ParsedHyp] = []
                for hyp in goal.hyps:
                    hyp_ast, hyp_text, num_read = self.__read_definition(
                        coq_file, num_definitions, num_read
                    )
                    parsed_hyp = ParsedHyp(hyp.names, hyp_ast, hyp_text)
                    parsed_hyps.append(parsed_hyp)
                goal_ast, goal_text, num_read = self.__read_definition(
                    coq_file, num_definitions, num_read
                )
                parsed_goal = ParsedObligation(parsed_hyps, goal_ast, goal_text)
                parsed_goals.append(parsed_goal)
        return ParsedObligations(parsed_goals)

    def check_proof(self, partial_proof: str) -> ProofCheckResult:
        # partial_steps = separate_steps(partial_proof)
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
            partial_steps = [s.text for s in coq_file.steps[(self.proof_point + 1) :]]
            try:
                assert "".join(partial_steps) == partial_proof
            except AssertionError:
                ipdb.set_trace()
            if len(partial_steps) > 0 and "Qed." in partial_steps[-1]:
                # We detect qed ourselves.
                partial_steps = partial_steps[:-1]
        try:
            self.set_proof_file(partial_steps)
            current_goals = self.proof_file.current_goals
        except InvalidChangeException:
            return ProofCheckResult.get_invalid()
        if self.proof_file.can_close_proof:
            parsed_obligations = None
            dset_file = None
            return ProofCheckResult(
                TacticResult.COMPLETE,
                partial_steps,
                current_goals,
                parsed_obligations,
                dset_file,
            )
        dset_file = self.get_dataset_file()
        assert current_goals is not None
        parsed_obligations = self.get_parsed_goals(partial_proof, current_goals)
        return ProofCheckResult(
            TacticResult.VALID,
            partial_steps,
            self.proof_file.current_goals,
            parsed_obligations,
            dset_file,
        )

    def get_example(self, dset_file: DatasetFile) -> LmExample:
        proof = dset_file.proofs[-1]
        last_step_idx = len(proof.steps) - 1
        example = self.lm_formatter.example_from_step(
            last_step_idx,
            proof,
            dset_file,
            self.file_info,
            self.split,
            self.data_loc,
        )
        return example

    def get_dataset_file(
        self,
    ) -> DatasetFile:
        self.proof_file.exec(1)  # Step past admitted
        last_proof = self.proof_file.proofs[-1]
        last_proof_data = get_last_proof_data_points(last_proof)
        context_list = list(self.proof_file.context.terms.values())
        context_data = get_context(context_list)
        proofs = DatasetFile.proofs_from_jsonl(last_proof_data)
        file_context_data = {
            "file": proc_file_path(last_proof.file_path),
            "workspace": proc_file_path(last_proof.file_path),
            "repository": "junkrepo",
            "context": context_data,
        }
        file_context = FileContext.from_json(file_context_data)
        self.proof_file.exec(-1)  # Return to before admitted (Point to last step)
        return DatasetFile(file_context, proofs)

    def __enter__(self) -> ProofManager:
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc_value: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        _logger.debug("Restoring proof file.")
        if os.path.exists(self.aux_file_path):
            os.remove(self.aux_file_path)
        self.__restore_proof_file()
