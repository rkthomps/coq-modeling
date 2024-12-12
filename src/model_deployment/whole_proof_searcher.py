from __future__ import annotations
from typing import Optional, Any
import time
from enum import Enum
from dataclasses import dataclass

from tactic_gen.lm_example import LmExample
from data_management.dataset_file import DatasetFile, Proof

from model_deployment.tactic_gen_client import TacticGenClient
from model_deployment.proof_manager import ProofManager
from model_deployment.proof_manager import TacticResult


@dataclass
class WholeProofSuccess:
    time: float
    model_time: float
    successful_proof: Proof
    attempted_proofs: list[str]
    costs: list[float]


@dataclass
class WholeProofFailure:
    time: float
    model_time: float
    attempted_proofs: list[str]
    costs: list[float]


class RecType(Enum):
    ALL_AT_ONCE = 0
    ONE_BY_ONE = 1

    @classmethod
    def from_string(cls, s: str) -> RecType:
        if s == "all_at_once":
            return cls.ALL_AT_ONCE
        elif s == "one_by_one":
            return cls.ONE_BY_ONE
        else:
            raise ValueError(f"Unknown rec type {s}")


@dataclass
class WholeProofSearcherConf:
    n_attempts: int
    print_proofs: bool
    rectype: RecType
    timeout = 600
    ALIAS = "whole_proof"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> WholeProofSearcherConf:
        return cls(
            yaml_data["n_attempts"],
            yaml_data["print_proofs"],
            RecType.from_string(yaml_data["rectype"]),
        )


class WholeProofSearcher:
    def __init__(
        self,
        tactic_gen_client: TacticGenClient,
        proof_manager: ProofManager,
        n_attempts: int,
        print_proofs: bool,
        rec_type: RecType,
    ):
        self.tactic_gen_client = tactic_gen_client
        self.proof_manager = proof_manager
        self.n_attempts = n_attempts
        self.print_proofs = print_proofs
        self.rec_type = rec_type

        initial_dset_file = proof_manager.get_initial_context()
        if initial_dset_file is None:
            raise ValueError("Could not get initial datasetfile")
        self.initial_dset_file = initial_dset_file

        initial_proof = ""
        self.total_model_time = 0

        self.initial_proof_obj = self.initial_dset_file.proofs[-1]
        self.initial_check_result = proof_manager.check_proof(
            initial_proof, self.initial_proof_obj.theorem
        )
        # print(initial_check_result)
        assert self.initial_check_result.tactic_result == TacticResult.VALID
        assert self.initial_check_result.current_goals is not None
        assert self.initial_check_result.new_proof is not None
        self.cur_dset_file = self.proof_manager.build_dset_file(
            self.initial_check_result.new_proof
        )

    @classmethod
    def from_conf(
        cls,
        conf: WholeProofSearcherConf,
        tactic_gen_clients: list[TacticGenClient],
        proof_manager: ProofManager,
    ) -> WholeProofSearcher:
        assert len(tactic_gen_clients) == 1
        return cls(
            tactic_gen_clients[0],
            proof_manager,
            conf.n_attempts,
            conf.print_proofs,
            conf.rectype,
        )

    @property
    def need_goal_record(self) -> bool:
        return False

    def search(self, **kwargs: Any) -> WholeProofSuccess | WholeProofFailure:
        match self.rec_type:
            case RecType.ALL_AT_ONCE:
                return self.search_all_at_once()
            case RecType.ONE_BY_ONE:
                return self.search_one_by_one()

    def search_all_at_once(self) -> WholeProofSuccess | WholeProofFailure:
        start_time = time.time()
        last_proof = self.cur_dset_file.proofs[-1]
        admitted_step = last_proof.steps[-1]
        cur_proof_script = last_proof.proof_prefix_to_string(
            admitted_step, include_theorem=False
        )
        start_model_time = time.time()
        result = self.tactic_gen_client.get_recs(
            len(last_proof.steps) - 1,
            last_proof,
            self.cur_dset_file,
            self.n_attempts,
            file_prefix=self.proof_manager.file_prefix,
        )
        end_model_time = time.time()
        self.total_model_time += end_model_time - start_model_time

        attempts: list[str] = []
        costs: list[float] = []
        for i, attempt in enumerate(result.next_tactic_list):
            if self.print_proofs:
                print(cur_proof_script + attempt)
            proof_check_result = self.proof_manager.check_proof(
                cur_proof_script + attempt, last_proof.theorem
            )
            attempts.append(cur_proof_script + attempt)
            costs.append(result.costs[i] if result.costs is not None else 0)
            match proof_check_result.tactic_result:
                case TacticResult.COMPLETE:
                    total_time = time.time() - start_time
                    assert proof_check_result.new_proof is not None
                    return WholeProofSuccess(
                        total_time,
                        self.total_model_time,
                        proof_check_result.new_proof,
                        attempts,
                        costs,
                    )
                case _:
                    continue
        total_time = time.time() - start_time
        return WholeProofFailure(total_time, self.total_model_time, attempts, costs)

    def search_one_by_one(self) -> WholeProofSuccess | WholeProofFailure:
        attempts: list[str] = []
        costs: list[float] = []
        start_time = time.time()
        for attempt_num in range(self.n_attempts):
            maybe_complete, attempt, cost = self.search_step()
            if self.print_proofs:
                print(f"Attempt ({cost}): ")
                print(attempt)

            attempts.append(attempt)
            costs.append(cost)
            if maybe_complete is not None:
                total_time = time.time() - start_time
                return WholeProofSuccess(
                    total_time,
                    self.total_model_time,
                    maybe_complete,
                    attempts,
                    costs,
                )
        total_time = time.time() - start_time
        return WholeProofFailure(total_time, self.total_model_time, attempts, costs)

    def search_step(self) -> tuple[Optional[Proof], str, float]:
        last_proof = self.cur_dset_file.proofs[-1]
        admitted_step = last_proof.steps[-1]
        cur_proof_script = last_proof.proof_prefix_to_string(
            admitted_step, include_theorem=False
        )
        start_time = time.time()
        result = self.tactic_gen_client.get_recs(
            len(last_proof.steps) - 1,
            last_proof,
            self.cur_dset_file,
            1,
            file_prefix=self.proof_manager.file_prefix,
        )
        end_time = time.time()
        assert len(result.next_tactic_list) == 1
        next_tactic = result.next_tactic_list[0]
        self.total_model_time += end_time - start_time
        proof_check_result = self.proof_manager.check_proof(
            cur_proof_script + next_tactic, last_proof.theorem
        )
        cost = result.costs[0] if result.costs is not None else 0
        match proof_check_result.tactic_result:
            case TacticResult.COMPLETE:
                return (
                    proof_check_result.new_proof,
                    cur_proof_script + next_tactic,
                    cost,
                )
            case _:
                return None, cur_proof_script + next_tactic, cost
