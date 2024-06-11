from __future__ import annotations
from typing import Optional, Any
import random
from dataclasses import dataclass
import math
import time

from coqpyt.coq.lsp.structs import Goal
from tactic_gen.lm_example import LmExample

from data_management.dataset_file import DatasetFile, Proof
from model_deployment.model_result import ModelResult, filter_recs
from proof_retrieval.mine_goals import GoalRecord
from model_deployment.goal_comparer import GoalScorer, AlphaGoalComparer
from model_deployment.proof_manager import ProofManager, TacticResult
from model_deployment.tactic_gen_client import TacticGenClient

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


@dataclass
class StraightLineSuccess:
    time: float
    model_time: float
    successful_proof: Proof
    attempted_proofs: list[str]


@dataclass
class StraightLineFailure:
    time: float
    model_time: float
    attempted_proofs: list[str]


@dataclass
class StraightLineSearcherConf:
    timeout: int
    print_proofs: bool
    initial_proof: Optional[str]
    ALIAS = "straight_line"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> StraightLineSearcherConf:
        return cls(
            yaml_data["timeout"],
            yaml_data["print_proofs"],
            yaml_data.get("initial_proof", None),
        )


class StraightLineSearcher:
    def __init__(
        self,
        tactic_client: TacticGenClient,
        proof_manager: ProofManager,
        timeout: int,
        print_proofs: bool,
        initial_proof: Optional[str] = None,
    ):
        self.tactic_client = tactic_client
        self.proof_manager = proof_manager
        self.timeout = timeout
        self.print_proofs = print_proofs
        self.initial_proof = initial_proof
        if 1 < len(self.tactic_client.formatters):
            _logger.warning(
                "More than one formatter in straight line searcher using first."
            )
        self.formatter = self.tactic_client.formatters[0]

        initial_dset_file = proof_manager.get_initial_context()
        if initial_dset_file is None:
            raise ValueError("Could not get initial datasetfile")
        self.initial_dset_file = initial_dset_file

        if initial_proof is None:
            initial_proof = ""
        self.need_goal_record = False
        self.total_model_time = 0

        self.initial_proof_obj = self.initial_dset_file.proofs[-1]
        self.initial_check_result = proof_manager.check_proof(
            initial_proof, self.initial_proof_obj.theorem, self.need_goal_record
        )
        # print(initial_check_result)
        assert self.initial_check_result.tactic_result == TacticResult.VALID
        assert self.initial_check_result.current_goals is not None
        assert self.initial_check_result.new_proof is not None

    @classmethod
    def from_conf(
        cls,
        conf: StraightLineSearcherConf,
        tactic_client: TacticGenClient,
        proof_manager: ProofManager,
    ) -> StraightLineSearcher:
        return cls(
            tactic_client,
            proof_manager,
            conf.timeout,
            conf.print_proofs,
            conf.initial_proof,
        )

    def build_dset_file(self, new_proof: Proof) -> DatasetFile:
        return DatasetFile(
            self.proof_manager.file_context,
            self.proof_manager.same_file_proofs + [new_proof],
        )

    def search(self, **kwargs) -> StraightLineSuccess | StraightLineFailure:
        start_time = time.time()
        attempts: list[str] = []
        cur_time = time.time() - start_time
        while cur_time < self.timeout:
            maybe_complete, attempt = self.search_step(start_time)
            if self.print_proofs:
                print(attempt)
            attempts.append(attempt)
            if maybe_complete is not None:
                total_time = time.time() - start_time
                return StraightLineSuccess(
                    total_time,
                    self.total_model_time,
                    maybe_complete,
                    attempts,
                )
            cur_time = time.time() - start_time
        return StraightLineFailure(cur_time, self.total_model_time, attempts)

    def search_step(self, start_time: float) -> tuple[Optional[Proof], str]:
        cur_proof_result = self.initial_check_result
        cur_time = time.time() - start_time
        last_proof_script = ""
        while (
            cur_proof_result.tactic_result == TacticResult.VALID
            and cur_time < self.timeout
        ):
            assert cur_proof_result.new_proof is not None
            cur_dset_file = self.build_dset_file(cur_proof_result.new_proof)
            admitted_step = cur_dset_file.proofs[-1].steps[-1]
            cur_proof_script = cur_dset_file.proofs[-1].proof_prefix_to_string(
                admitted_step, include_theorem=False
            )
            example = self.proof_manager.get_example(
                self.formatter, cur_dset_file, cur_proof_result.goal_record
            )
            start_model_time = time.time()
            result = self.tactic_client.get_recs(example, 1, cur_proof_script)
            end_model_time = time.time()
            assert len(result.next_tactic_list) == 1
            next_tactic = result.next_tactic_list[0]
            self.total_model_time += end_model_time - start_model_time
            proof_check_result = self.proof_manager.check_proof(
                cur_proof_script + next_tactic,
                cur_proof_result.new_proof.theorem,
                False,
            )
            last_proof_script = cur_proof_script + next_tactic
            cur_proof_result = proof_check_result
            cur_time = time.time() - start_time

        match cur_proof_result.tactic_result:
            case TacticResult.VALID:
                return None, last_proof_script
            case TacticResult.INVALID:
                return None, last_proof_script
            case TacticResult.COMPLETE:
                assert cur_proof_result.new_proof is not None
                return cur_proof_result.new_proof, last_proof_script
