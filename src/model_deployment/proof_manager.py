from __future__ import annotations
from typing import Any, Optional
from types import TracebackType

import os
import shutil
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
    def get_invalid(cls, attempted_steps: list[str]) -> ProofCheckResult:
        current_goals = None
        goal_record = None
        new_dataset_file = None
        return cls(
            TacticResult.INVALID,
            attempted_steps,
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
    SEARCH_DIR = Path("./.cm-search")

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

    def __make_empty(self, p: Path):
        with open(p, "w") as fout:
            pass

    def __start_clients(self) -> None:
        if not self.SEARCH_DIR.exists():
            os.makedirs(self.SEARCH_DIR)
        self.fast_aux_file_path = get_fresh_path(
            self.SEARCH_DIR, str(self.file_loc.name)
        ).resolve()
        self.__make_empty(self.fast_aux_file_path)
        self.fast_aux_client = FastLspClient(self.workspace_uri, timeout=60)
        fast_aux_file_uri = f"file://{self.fast_aux_file_path}"
        self.fast_goal_file_path = get_fresh_path(
            self.SEARCH_DIR, "goal_" + str(self.file_loc.name)
        ).resolve()
        self.__make_empty(self.fast_goal_file_path)
        fast_goal_file_uri = f"file://{self.fast_goal_file_path}"
        self.fast_client = ClientWrapper(self.fast_aux_client, fast_aux_file_uri)
        self.goal_client = ClientWrapper(self.fast_aux_client, fast_goal_file_uri)

    def __restart_clients(self) -> None:
        if os.path.exists(self.fast_aux_file_path):
            os.remove(self.fast_aux_file_path)
        if os.path.exists(self.fast_goal_file_path):
            os.remove(self.fast_goal_file_path)
        # self.fast_aux_client.shutdown()
        # self.fast_aux_client.exit()
        self.fast_aux_client.kill()
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
        self,
        cur_steps: list[str],
        cur_goals: GoalAnswer,
        theorem: dataset_file.Term,
        complete: bool = False,
    ) -> Proof:
        focused_steps: list[FocusedStep] = []
        for i, step in enumerate(cur_steps):
            focused_steps.append(
                FocusedStep(theorem, Step.from_text(step, TermType.TACTIC), i, [])
            )

        goals = [dataset_file.Goal.from_json(repr(g)) for g in cur_goals.goals.goals]
        if complete:
            new_step = FocusedStep(
                theorem,
                Step.from_text("\nQed.", TermType.TACTIC),
                len(cur_steps),
                goals,
            )
        else:
            new_step = FocusedStep(
                theorem,
                Step.from_text("\nAdmitted.", TermType.TACTIC),
                len(cur_steps),
                goals,
            )
        focused_steps.append(new_step)
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
            self.goal_client.client,
            self.goal_client.file_uri,
            self.goal_client.file_version,
            end_pos,
            steps,
            new_step_idx,
            goal_dict,
        )
        self.goal_client.set_version(version)
        return record

    def gather_steps(self, steps: list[CStep]) -> tuple[list[CStep], list[CStep]]:
        agg_str = ""
        cur_idx = 0
        for s in steps:
            agg_str += s.text
            if not self.file_prefix.startswith(agg_str):
                break
            cur_idx += 1
        prefix_steps = steps[:cur_idx]
        new_steps = steps[cur_idx:]
        parsed_prefix = "".join([s.text for s in prefix_steps])
        if parsed_prefix != self.file_prefix:
            _logger.error(
                f"INCOMPATIBLE STEPS; NEW LEN: {len(prefix_steps)}; OLD_LEN: {len(self.proof_info.prefix_steps)}"
            )
        assert parsed_prefix == self.file_prefix
        return prefix_steps, new_steps

    def check_proof(
        self,
        partial_proof: str,
        theorem: dataset_file.Term,
        need_goal_record: bool = True,
    ) -> ProofCheckResult:
        if (
            ("Theorem" in partial_proof)
            or ("Lemma" in partial_proof)
            or ("Proposition" in partial_proof)
            or ("Remark" in partial_proof)
            or ("Corollary" in partial_proof)
            or ("Property" in partial_proof)
            or ("Admitted." in partial_proof)
            or ("admit." in partial_proof)
            or ("Abort." in partial_proof)
        ):
            return ProofCheckResult.get_invalid([])
        contents = f"{self.file_prefix}{partial_proof}"
        try:
            steps = self.fast_client.write_and_get_steps(contents)
        except ResponseError as e:
            _logger.warning(f"Got repsonse error on proof: {partial_proof[-30:]}")
            self.__restart_clients()
            return ProofCheckResult.get_invalid([])
        except TimeoutError as t:
            _logger.warning(f"Got timeout error on proof: {partial_proof[-30:]}")
            self.__restart_clients()
            return ProofCheckResult.get_invalid([])

        if not self.check_valid(self.fast_client.client):
            return ProofCheckResult.get_invalid([s.text for s in steps])

        if 0 < len(partial_proof) and "Qed." in steps[-1].text:
            steps = steps[:-1]  # We detect qed ourselves.

        prefix_steps, new_steps = self.gather_steps(steps)
        new_step_strs = [s.text for s in new_steps]

        farther_end = steps[-1].ast.range.end
        try:
            current_goals = self.fast_client.client.proof_goals(
                TextDocumentIdentifier(self.fast_client.file_uri), farther_end
            )
        except ResponseError as e:
            _logger.warning(f"Got repsonse error on proof: {partial_proof[-10:]}")
            self.__restart_clients()
            return ProofCheckResult.get_invalid(new_step_strs)
        except TimeoutError as t:
            _logger.warning(f"Got timeout error on proof: {partial_proof[-10:]}")
            self.__restart_clients()
            return ProofCheckResult.get_invalid(new_step_strs)
        self.fast_client.client.lsp_endpoint.timeout = 5

        if current_goals is None:
            return ProofCheckResult.get_invalid(new_step_strs)
        if current_goals.goals is None:
            return ProofCheckResult.get_invalid(new_step_strs)

        if self.__can_close_proof(current_goals):
            goal_record = None
            must_be_valid = "".join([s.text for s in steps]) + "\nQed."
            steps = self.fast_client.write_and_get_steps(must_be_valid)
            if not self.check_valid(self.fast_client.client):
                return ProofCheckResult.get_invalid(new_step_strs)
            new_proof = self.get_proof_shell(
                new_step_strs, current_goals, theorem, complete=True
            )
            return ProofCheckResult(
                TacticResult.COMPLETE,
                new_step_strs,
                get_all_goals(current_goals),
                goal_record,
                new_proof,
            )

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

        new_proof = self.get_proof_shell(new_step_strs, current_goals, theorem)
        return ProofCheckResult(
            TacticResult.VALID,
            new_step_strs,
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
        if self.fast_goal_file_path.exists():
            os.remove(self.fast_goal_file_path)
        self.fast_aux_client.kill()
        # self.fast_aux_client.shutdown()
        # self.fast_aux_client.exit()
