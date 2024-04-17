from __future__ import annotations
from typing import Any, Optional
from types import TracebackType

import os
from pathlib import Path
from enum import Enum
from dataclasses import dataclass
import ipdb
import time


from util.util import get_fresh_path
from data_management import dataset_file
from data_management.splits import DataSplit
from data_management.sentence_db import SentenceDB
from data_management.dataset_file import (
    DatasetFile,
    Proof,
    Term,
    FocusedStep,
    Step,
    FileContext,
)
from data_management.splits import Split, FileInfo

from tactic_gen.lm_example import (
    LmExample,
    LmFormatter,
    ProofRetrievalFormatter,
    GPTProofFormatter,
)

from model_deployment.fast_client import FastLspClient, ClientWrapper
from model_deployment.mine_goals import get_goal_record, GoalRecord
from util.coqpyt_utils import get_all_goals
from util.util import get_basic_logger

from coqpyt.coq.lsp.client import (
    TextDocumentIdentifier,
    Position,
)
from coqpyt.coq.structs import ProofTerm, Term as CTerm, TermType, Step as CStep
from coqpyt.coq.lsp.structs import Goal, GoalAnswer, RangedSpan
from coqpyt.lsp.structs import ResponseError

from coqpyt.lsp.structs import (
    TextDocumentIdentifier,
    Position,
    Range,
)


_logger = get_basic_logger(__name__)


class TacticResult(Enum):
    COMPLETE = 1
    VALID = 2
    INVALID = 3


@dataclass
class ProofCheckResult:
    tactic_result: TacticResult
    attempted_steps: list[str]
    current_goals: Optional[list[Goal]]
    goal_record: Optional[GoalRecord]
    new_proof: Optional[Proof]

    @classmethod
    def get_invalid(cls) -> ProofCheckResult:
        current_goals = None
        goal_record = None
        new_dataset_file = None
        return cls(
            TacticResult.INVALID,
            [],
            current_goals,
            goal_record,
            new_dataset_file,
        )


@dataclass
class ProofInfo:
    proof_term: Term
    prefix_steps: list[CStep]
    proof_point: int


class ProofManager:
    TIMEOUT = 60

    def __init__(
        self,
        file_context: FileContext,
        proof_info: ProofInfo,
        file_info: FileInfo,
        sentence_db: SentenceDB,
        split: Split,
        data_loc: Path,
    ) -> None:
        self.file_context = file_context
        self.proof_info = proof_info
        self.file_info = file_info
        self.sentence_db = sentence_db
        self.split = split
        self.data_loc = data_loc
        self.__start_clients()

    def __start_clients(self) -> None:
        self.fast_aux_file_path = get_fresh_path(
            Path("."), str(self.file_loc.name)
        ).resolve()
        fast_aux_client = FastLspClient(self.workspace_uri, timeout=60)
        fast_aux_file_uri = f"file://{self.fast_aux_file_path}"
        self.fast_client = ClientWrapper(fast_aux_client, fast_aux_file_uri)

    def __restart_clients(self) -> None:
        if os.path.exists(self.fast_aux_file_path):
            os.remove(self.fast_aux_file_path)
        self.fast_client.close()
        self.__start_clients()

    @property
    def file_prefix(self) -> str:
        return "".join([s.text for s in self.proof_info.prefix_steps])

    @property
    def file_loc(self) -> Path:
        return self.data_loc / self.file_info.file

    @property
    def workspace_uri(self) -> str:
        return f"file://{(self.data_loc / self.file_info.workspace).resolve()}"

    def get_proof_shell(
        self, cur_steps: list[str], cur_goals: GoalAnswer, theorem: dataset_file.Term
    ) -> Proof:
        focused_steps: list[FocusedStep] = []
        for i, step in enumerate(cur_steps):
            focused_steps.append(
                FocusedStep(theorem, Step.from_text(step, TermType.TACTIC), i, [])
            )

        goals = [dataset_file.Goal.from_json(repr(g)) for g in cur_goals.goals.goals]
        focused_steps.append(
            FocusedStep(
                theorem,
                Step.from_text("\nAdmitted.", TermType.TACTIC),
                len(cur_steps),
                goals,
            )
        )
        proof = Proof(theorem, focused_steps)
        return proof

    def __can_close_proof(self, goals: Optional[GoalAnswer]):
        def empty_stack(stack: list[tuple[list[Goal], list[Goal]]]):
            # e.g. [([], [])]
            for tuple in stack:
                if len(tuple[0]) > 0 or len(tuple[1]) > 0:
                    return False
            return True

        if goals is None:
            return False

        inner_goals = goals.goals
        if inner_goals is None:
            return False

        return (
            len(inner_goals.goals) == 0
            and empty_stack(inner_goals.stack)
            and len(inner_goals.shelf) == 0
            and inner_goals.bullet is None
        )

    def get_initial_context(self) -> Optional[DatasetFile]:
        initial_proof_result = self.check_proof("", self.proof_info.proof_term)
        assert initial_proof_result.new_proof is not None
        return DatasetFile(self.file_context, [initial_proof_result.new_proof])

    def check_valid(self, client: FastLspClient) -> bool:
        for diagnostic in client.lsp_endpoint.diagnostics[self.fast_client.file_uri]:
            if diagnostic.severity == 1:
                return False
        return True

    def get_goal_record(self, steps: list[CStep]) -> Optional[GoalRecord]:
        new_step_idx = len(steps) - 1
        end_pos = steps[new_step_idx].ast.range.end
        goal_dict: dict[int, Optional[GoalAnswer]] = {}
        record, version = get_goal_record(
            self.fast_client.client,
            self.fast_client.file_uri,
            self.fast_client.file_version,
            end_pos,
            steps,
            new_step_idx,
            goal_dict,
        )
        self.fast_client.set_version(version)
        return record

    def check_proof(
        self,
        partial_proof: str,
        theorem: dataset_file.Term,
        need_goal_record: bool = True,
    ) -> ProofCheckResult:
        # TODO: NEED TO CATCH SIMPL IN *
        # partial_steps = separate_steps(partial_proof)
        if (
            ("Theorem" in partial_proof)
            or ("Admitted." in partial_proof)
            or ("admit." in partial_proof)
            or ("Abort." in partial_proof)
        ):
            return ProofCheckResult.get_invalid()
        contents = f"{self.file_prefix}{partial_proof}"
        try:
            steps = self.fast_client.write_and_get_steps(contents)
        except ResponseError as e:
            _logger.warning(f"Got repsonse error on proof: {partial_proof[-30:]}")
            self.__restart_clients()
            return ProofCheckResult.get_invalid()
        except TimeoutError as t:
            _logger.warning(f"Got timeout error on proof: {partial_proof[-30:]}")
            self.__restart_clients()
            return ProofCheckResult.get_invalid()

        if not self.check_valid(self.fast_client.client):
            return ProofCheckResult.get_invalid()
        partial_steps = [s.text for s in steps[(self.proof_info.proof_point + 1) :]]
        # end_pos = steps[-1].ast.range.end
        num_lines = len(contents.split("\n"))
        if 0 < len(partial_proof) and "Qed." in steps[-1].text:
            # We detect qed ourselves.
            steps = steps[:-1]

        farther_end = steps[-1].ast.range.end
        try:
            current_goals = self.fast_client.client.proof_goals(
                TextDocumentIdentifier(self.fast_client.file_uri), farther_end
            )
        except ResponseError as e:
            _logger.warning(f"Got repsonse error on proof: {partial_proof[-10:]}")
            self.__restart_clients()
            return ProofCheckResult.get_invalid()
        except TimeoutError as t:
            _logger.warning(f"Got timeout error on proof: {partial_proof[-10:]}")
            self.__restart_clients()
            return ProofCheckResult.get_invalid()
        self.fast_client.client.lsp_endpoint.timeout = 5

        if current_goals is None:
            return ProofCheckResult.get_invalid()
        if current_goals.goals is None:
            return ProofCheckResult.get_invalid()

        # try:
        #     assert "".join(partial_steps) == partial_proof
        # except AssertionError:
        #     act = "".join(partial_steps)
        #     exp = partial_proof
        #     _logger.warning(f"Partial proof mismatch: expected '{exp}' got '{act}'")
        #     # ipdb.set_trace()

        if self.__can_close_proof(current_goals):
            goal_record = None
            proof = None
            return ProofCheckResult(
                TacticResult.COMPLETE,
                partial_steps,
                get_all_goals(current_goals),
                goal_record,
                proof,
            )

        new_proof = self.get_proof_shell(partial_steps, current_goals, theorem)
        try:
            goal_record = None
            if need_goal_record:
                goal_record = self.get_goal_record(steps)
        except ResponseError as e:
            _logger.warning(f"Got repsonse getting goal record: {partial_proof[-10:]}")
            self.__restart_clients()
            goal_record = None
        except TimeoutError as t:
            _logger.warning(
                f"Got timeout error getting goal record: {partial_proof[-10:]}"
            )
            self.__restart_clients()
            goal_record = None
        except TypeError as t:
            _logger.warning(
                f"Got type error getting goal record: {partial_proof[-10:]}"
            )
            goal_record = None

        return ProofCheckResult(
            TacticResult.VALID,
            partial_steps,
            get_all_goals(current_goals),
            goal_record,
            new_proof,
        )

    def get_example(
        self,
        formatter: LmFormatter,
        dset_file: DatasetFile,
        goal_record: Optional[GoalRecord],
    ) -> LmExample:
        proof = dset_file.proofs[-1]
        last_step_idx = len(proof.steps) - 1
        example = formatter.example_from_step(
            last_step_idx,
            proof,
            dp_obj=dset_file,
            file_info=self.file_info,
            split=self.split,
            data_loc=self.data_loc,
            ground_truth_steps=None,  # Not doing this right now
            key_record=goal_record,
            cutoff_idx=self.proof_info.proof_point,
        )
        # print(example.input)
        # print(example.passages)
        return example

    def __enter__(self) -> ProofManager:
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc_value: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        _logger.debug("Restoring proof file.")
        # if os.path.exists(self.aux_file_path):
        #     os.remove(self.aux_file_path)
        # self.aux_client.close()
        if os.path.exists(self.fast_aux_file_path):
            os.remove(self.fast_aux_file_path)
        self.fast_client.close()
