from __future__ import annotations
from typing import Any, Optional
from types import TracebackType

import os
from pathlib import Path
from enum import Enum
from dataclasses import dataclass


from util.util import get_fresh_path
from util.coqpyt_utils import get_all_goals
from util.constants import TMP_LOC, SEARCH_DIR_NAME
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
)

from model_deployment.fast_client import FastLspClient, ClientWrapper
from util.constants import RANGO_LOGGER

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

import logging

_logger = logging.getLogger(RANGO_LOGGER)


class TacticResult(Enum):
    COMPLETE = 1
    VALID = 2
    INVALID = 3


@dataclass
class ProofCheckResult:
    tactic_result: TacticResult
    attempted_steps: list[str]
    current_goals: Optional[list[Goal]]
    new_proof: Optional[Proof]
    steps: Optional[list[CStep]]

    @classmethod
    def get_invalid(cls, attempted_steps: list[str]) -> ProofCheckResult:
        current_goals = None
        new_dataset_file = None
        return cls(
            TacticResult.INVALID,
            attempted_steps,
            current_goals,
            new_dataset_file,
            None,
        )


@dataclass
class ProofInfo:
    proof_term: Term
    prefix_steps: list[CStep]
    proof_point: int


class ProofManager:
    SEARCH_DIR = TMP_LOC / SEARCH_DIR_NAME

    def __init__(
        self,
        file_context: FileContext,
        same_file_proofs: list[Proof],
        proof_info: ProofInfo,
        file_loc: Path,
        workspace_loc: Path,
        sentence_db: SentenceDB,
        data_loc: Path,
    ) -> None:
        self.same_file_proofs = same_file_proofs
        self.file_context = file_context
        self.proof_info = proof_info
        self.file_loc = file_loc
        self.workspace_loc = workspace_loc
        self.sentence_db = sentence_db
        self.data_loc = data_loc
        self.__start_clients()

    def __make_empty(self, p: Path):
        with open(p, "w") as fout:
            pass

    def __start_clients(self) -> None:
        if not self.SEARCH_DIR.exists():
            os.makedirs(self.SEARCH_DIR)
        self.fast_aux_file_path = get_fresh_path(
            self.file_loc.parent, "aux_" + str(self.file_loc.name)
        ).resolve()
        self.__make_empty(self.fast_aux_file_path)
        self.fast_aux_client = FastLspClient(self.workspace_uri, timeout=600)
        fast_aux_file_uri = f"file://{self.fast_aux_file_path}"
        self.fast_client = ClientWrapper(self.fast_aux_client, fast_aux_file_uri)

    def __restart_clients(self) -> None:
        if os.path.exists(self.fast_aux_file_path):
            os.remove(self.fast_aux_file_path)
        # self.fast_aux_client.shutdown()
        # self.fast_aux_client.exit()
        self.fast_aux_client.kill()
        self.__start_clients()

    @property
    def file_prefix(self) -> str:
        return "".join([s.text for s in self.proof_info.prefix_steps])

    @property
    def workspace_uri(self) -> str:
        return f"file://{(self.workspace_loc).resolve()}"

    def get_proof_shell(
        self,
        cur_steps: list[str],
        cur_goals: GoalAnswer,
        theorem: dataset_file.Term,
        complete: bool = False,
    ) -> Proof:
        focused_steps: list[FocusedStep] = []
        assert self.first_goals is not None
        orig_goals = [
            dataset_file.Goal.from_json(repr(g)) for g in self.first_goals.goals.goals
        ]
        for i, step in enumerate(cur_steps):
            step_goals = orig_goals if i == 0 else []
            focused_steps.append(
                FocusedStep(
                    theorem, Step.from_text(step, TermType.TACTIC), i, step_goals
                )
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
        proof = Proof(theorem, focused_steps, len(self.same_file_proofs))
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
        # TODO ADD PREFIX TO THIS DSET FILE
        initial_proof_result = self.check_proof(
            "", self.proof_info.proof_term, initial_proof=True
        )
        print("Tactic result:", initial_proof_result.tactic_result)
        assert initial_proof_result.new_proof is not None
        return DatasetFile(
            self.file_context, self.same_file_proofs + [initial_proof_result.new_proof]
        )

    def build_dset_file(self, new_proof: Proof) -> DatasetFile:
        return DatasetFile(
            self.file_context,
            self.same_file_proofs + [new_proof],
        )

    def check_valid(self, client: FastLspClient) -> bool:
        for diagnostic in client.lsp_endpoint.diagnostics[self.fast_client.file_uri]:
            if diagnostic.severity == 1:
                print(diagnostic.message)
                return False
        return True

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
        initial_proof: bool = False,
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
        # self.fast_client.client.lsp_endpoint.timeout = 5

        if current_goals is None:
            return ProofCheckResult.get_invalid(new_step_strs)
        if current_goals.goals is None:
            return ProofCheckResult.get_invalid(new_step_strs)

        if initial_proof:
            self.first_goals = current_goals

        if self.__can_close_proof(current_goals):
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
                new_proof,
                steps,
            )

        new_proof = self.get_proof_shell(new_step_strs, current_goals, theorem)
        return ProofCheckResult(
            TacticResult.VALID,
            new_step_strs,
            get_all_goals(current_goals),
            new_proof,
            None,
        )

    def get_example(
        self,
        formatter: LmFormatter,
        dset_file: DatasetFile,
    ) -> LmExample:
        last_proof_idx = len(dset_file.proofs) - 1
        proof = dset_file.proofs[last_proof_idx]
        last_step_idx = len(proof.steps) - 1
        example = formatter.example_from_step(
            last_step_idx,
            last_proof_idx,
            dp_obj=dset_file,
            data_loc=self.data_loc,
            ground_truth_steps=None,  # Not doing this right now
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
        self.fast_aux_client.kill()
        # self.fast_aux_client.shutdown()
        # self.fast_aux_client.exit()
