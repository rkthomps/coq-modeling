from __future__ import annotations
from typing import Any, Optional
from types import TracebackType

import sys, os
from enum import Enum
import ipdb
import time
import logging

from typeguard import typechecked

from util.util import get_fresh_path
from util.coqpyt_utils import (
    replace_proof_with_admitted_stub,
    restore_proof_file,
    go_through_point,
)
from data_management import dataset_file
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

from tactic_gen.lm_example import LmExample, LmFormatter, ProofRetrievalFormatter

from model_deployment.goal_comparer import ParsedObligations, ParsedObligation, ParsedHyp 
from model_deployment.fast_client import FastLspClient, ClientWrapper
from model_deployment.mine_goals import get_goal_record, GoalRecord
from model_deployment.step_separator import separate_steps
from util.coqpyt_utils import get_all_goals
from util.util import LOGGER

from coqpyt.lsp.client import LspClient
from coqpyt.coq.lsp.client import (
    TextDocumentIdentifier,
    TextDocumentItem,
    CoqLspClient,
    Position,
)
from coqpyt.coq.changes import CoqAddStep, CoqDeleteStep
from coqpyt.coq.structs import ProofTerm, Term as CTerm, TermType, Step as CStep
from coqpyt.coq.lsp.structs import Goal, GoalAnswer, RangedSpan
from coqpyt.lsp.structs import ResponseError
from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.exceptions import InvalidChangeException

from coqpyt.lsp.structs import (
    TextDocumentIdentifier,
    VersionedTextDocumentIdentifier,
    TextDocumentContentChangeEvent,
    TextDocumentItem,
    Position,
    Range,
)



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
        current_goals: Optional[list[Goal]],
        goal_record: Optional[GoalRecord],
        new_proof: Optional[Proof],
    ) -> None:
        self.tactic_result = tactic_result
        self.attempted_steps = attempted_steps
        self.current_goals = current_goals
        self.goal_record = goal_record
        self.new_proof = new_proof

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



@typechecked
class ProofManager:
    TIMEOUT = 60

    def __init__(
        self,
        file_path: str,
        file_context: FileContext,
        proof_term: Term,
        prefix_steps: list[CStep],
        proof_point: int,
        lm_formatter: LmFormatter,
        file_info: FileInfo,
        sentence_db: SentenceDB,
        split: Split,
        data_loc: str,
    ) -> None:
        self.file_path = file_path
        self.lm_formatter = lm_formatter

        self.sentence_db = sentence_db

        self.file_info = file_info
        self.split = split
        self.data_loc = data_loc

        self.__workspace_loc = os.path.abspath(os.path.join(self.data_loc, self.file_info.workspace))
        self.prefix_steps = prefix_steps
        self.file_prefix = "".join([s.text for s in prefix_steps]) 
        self.proof_term = proof_term
        self.proof_point = proof_point
        self.file_context = file_context

        self.workspace_uri= f"file://{self.__workspace_loc}"
        self.__start_clients()


        # self.goal_file_path = get_fresh_path(file_dir, "aux_goals.v")
        # self.goal_file_uri = f"file://{self.goal_file_path}"
        # self.goal_client_root_version = 1
        # self.aux_client.didOpen(
        #     TextDocumentItem(
        #         self.goal_file_uri, "coq", self.goal_file_version, self.file_prefix
        #     )
        # )
    def __restart_clients(self) -> None:
        #self.aux_client.close()
        if os.path.exists(self.fast_aux_file_path):
            os.remove(self.fast_aux_file_path)
        self.fast_client.close()
        self.__start_clients()
    
    def __start_clients(self) -> None:
        file_dir = os.path.dirname(self.file_path)
        file_basename = os.path.basename(self.file_path)
        self.fast_aux_file_path = os.path.abspath(get_fresh_path(file_dir, f"aux_fast_{file_basename}"))
        fast_aux_client = FastLspClient(self.workspace_uri, timeout=60)
        fast_aux_file_uri = f"file://{self.fast_aux_file_path}"
        self.fast_client = ClientWrapper(fast_aux_client, fast_aux_file_uri)

        # self.aux_file_path = os.path.abspath(get_fresh_path(file_dir, f"aux_{file_basename}"))
        # aux_file_uri = f"file://{self.aux_file_path}"
        # aux_client = CoqLspClient(self.workspace_uri, timeout=2)
        # self.aux_client = ClientWrapper(aux_client, aux_file_uri)


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
        initial_proof_result = self.check_proof("", self.proof_term)
        assert initial_proof_result.new_proof is not None
        return DatasetFile(self.file_context, [initial_proof_result.new_proof])

    
    def check_valid(self, client: FastLspClient) -> bool:
        for diagnostic in client.lsp_endpoint.diagnostics[self.fast_client.file_uri]:
            if diagnostic.severity == 1:
                return False
        return True

    def get_goal_record(self, steps: list[CStep]) -> Optional[GoalRecord]:
        if not isinstance(self.lm_formatter, ProofRetrievalFormatter):
            return None
        new_step_idx = self.proof_point + len(steps)
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
        self, partial_proof: str, theorem: dataset_file.Term
    ) -> ProofCheckResult:
        # TODO: NEED TO CATCH SIMPL IN *
        # partial_steps = separate_steps(partial_proof)
        if (
            ("Admitted." in partial_proof)
            or ("admit." in partial_proof)
            or ("Abort." in partial_proof)
        ):
            return ProofCheckResult.get_invalid()
        t1 = time.time()
        contents = f"{self.file_prefix}{partial_proof}"
        try:
            steps = self.fast_client.write_and_get_steps(contents)
        except ResponseError:
            self.__restart_clients()
            return ProofCheckResult.get_invalid()
        except TimeoutError:
            self.__restart_clients()
            return ProofCheckResult.get_invalid()

        if not self.check_valid(self.fast_client.client):
            return ProofCheckResult.get_invalid()
        partial_steps = [s.text for s in steps[(self.proof_point + 1) :]]
        #end_pos = steps[-1].ast.range.end
        num_lines = len(contents.split("\n"))
        farther_end = Position(num_lines + 1, 0)
        try:
            current_goals = self.fast_client.client.proof_goals(TextDocumentIdentifier(self.fast_client.file_uri), farther_end) 
        except ResponseError:
            self.__restart_clients()
            return ProofCheckResult.get_invalid()
        except TimeoutError:
            self.__restart_clients()
            return ProofCheckResult.get_invalid()

        if current_goals is None:
            return ProofCheckResult.get_invalid() 
        t2 = time.time()

        self.fast_client.client.lsp_endpoint.timeout = 0.5
        print("New check time:", t2 - t1)

        # try:
        #     assert "".join(partial_steps) == partial_proof
        # except AssertionError:
        #     act = "".join(partial_steps)
        #     exp = partial_proof
        #     _logger.warning(f"Partial proof mismatch: expected '{exp}' got '{act}'")
        #     # ipdb.set_trace()

        if 0 < len(partial_proof) and "Qed." in steps[-1].text:
            # We detect qed ourselves.
            steps = steps[:-1]

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
        goal_record = self.get_goal_record(steps)
        return ProofCheckResult(
            TacticResult.VALID,
            partial_steps,
            get_all_goals(current_goals),
            goal_record,
            new_proof,
        )

    def get_example(
        self, dset_file: DatasetFile, goal_record: Optional[GoalRecord]
    ) -> LmExample:
        proof = dset_file.proofs[-1]
        last_step_idx = len(proof.steps) - 1
        example = self.lm_formatter.example_from_step(
            last_step_idx,
            proof,
            dp_obj=dset_file,
            file_info=self.file_info,
            split=self.split,
            data_loc=self.data_loc,
            ground_truth_steps=None, # Not doing this right now
            key_record=goal_record,
            cutoff_idx=self.proof_point,
        )
        return example

    def __enter__(self) -> ProofManager:
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc_value: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        LOGGER.debug("Restoring proof file.")
        # if os.path.exists(self.aux_file_path):
        #     os.remove(self.aux_file_path)
        # self.aux_client.close()
        if os.path.exists(self.fast_aux_file_path):
            os.remove(self.fast_aux_file_path)
        self.fast_client.close()
