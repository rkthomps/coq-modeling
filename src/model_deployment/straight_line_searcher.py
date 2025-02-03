from __future__ import annotations
from typing import Optional, Any
import random
from dataclasses import dataclass
import math
import time
import ipdb

from data_management.dataset_file import DatasetFile, Proof
from model_deployment.proof_manager import ProofManager, TacticResult
from model_deployment.tactic_gen_client import TacticGenClient

import logging
from util.constants import RANGO_LOGGER

_logger = logging.getLogger(RANGO_LOGGER)


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
    token_mask: Optional[str]
    interleave_hammer: bool
    ALIAS = "straight_line"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> StraightLineSearcherConf:
        return cls(
            yaml_data["timeout"],
            yaml_data["print_proofs"],
            yaml_data.get("initial_proof", None),
            yaml_data.get("token_mask", None),
            yaml_data.get("interleave_hammer", False),
        )


class StraightLineSearcher:
    def __init__(
        self,
        tactic_clients: list[TacticGenClient],
        proof_manager: ProofManager,
        timeout: int,
        print_proofs: bool,
        initial_proof: Optional[str],
        token_mask: Optional[str],
        interleave_hammer: bool = False,
    ):
        self.tactic_clients = tactic_clients
        self.proof_manager = proof_manager
        self.timeout = timeout
        self.print_proofs = print_proofs
        self.initial_proof = initial_proof
        self.token_mask = token_mask
        self.interleave_hammer = interleave_hammer

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
            initial_proof, self.initial_proof_obj.theorem
        )
        # print(initial_check_result)
        assert self.initial_check_result.tactic_result == TacticResult.VALID
        assert self.initial_check_result.current_goals is not None
        assert self.initial_check_result.new_proof is not None

    @classmethod
    def from_conf(
        cls,
        conf: StraightLineSearcherConf,
        tactic_clients: list[TacticGenClient],
        proof_manager: ProofManager,
    ) -> StraightLineSearcher:
        return cls(
            tactic_clients,
            proof_manager,
            conf.timeout,
            conf.print_proofs,
            conf.initial_proof,
            conf.token_mask,
            conf.interleave_hammer,
        )

    def search(self, **kwargs) -> StraightLineSuccess | StraightLineFailure:
        start_time = time.time()
        attempts: list[str] = []
        cur_time = time.time() - start_time
        while cur_time < self.timeout:
            maybe_complete, attempt = self.search_step(
                start_time,
                self.tactic_clients[len(attempts) % len(self.tactic_clients)],
            )
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

    def search_step(
        self, start_time: float, client: TacticGenClient
    ) -> tuple[Optional[Proof], str]:
        cur_proof_result = self.initial_check_result
        cur_time = time.time() - start_time
        last_proof_script = ""
        while (
            cur_proof_result.tactic_result == TacticResult.VALID
            and cur_time < self.timeout
        ):
            assert cur_proof_result.new_proof is not None
            cur_dset_file = self.proof_manager.build_dset_file(
                cur_proof_result.new_proof
            )
            admitted_step = cur_dset_file.proofs[-1].steps[-1]
            cur_proof_script = cur_dset_file.proofs[-1].proof_prefix_to_string(
                admitted_step, include_theorem=False
            )
            start_model_time = time.time()
            last_proof = cur_dset_file.proofs[-1]
            result = client.get_recs(
                len(last_proof.steps) - 1,
                last_proof,
                cur_dset_file,
                1,
                token_mask=self.token_mask,
                file_prefix=self.proof_manager.file_prefix,
            )
            end_model_time = time.time()
            assert len(result.next_tactic_list) == 1
            next_tactic = result.next_tactic_list[0]
            self.total_model_time += end_model_time - start_model_time
            proof_check_result = self.proof_manager.check_proof(
                cur_proof_script + next_tactic,
                cur_proof_result.new_proof.theorem,
            )
            last_proof_script = cur_proof_script + next_tactic
            cur_proof_result = proof_check_result
            cur_time = time.time() - start_time

            if (
                self.interleave_hammer
                and cur_proof_result.tactic_result == TacticResult.VALID
            ):
                print("RUNNING HAMMER!!")
                assert cur_proof_result.new_proof is not None
                hammer_script = (
                    last_proof_script
                    + "\nFrom Hammer Require Import Hammer.\nSet Hammer ATPLimit 5.\nall: hammer."
                )
                hammer_result = self.proof_manager.check_proof(
                    hammer_script, cur_proof_result.new_proof.theorem
                )
                match hammer_result.tactic_result:
                    case TacticResult.COMPLETE:
                        assert hammer_result.new_proof is not None
                        return (hammer_result.new_proof, hammer_script)

        match cur_proof_result.tactic_result:
            case TacticResult.VALID:
                return None, last_proof_script
            case TacticResult.INVALID:
                return None, last_proof_script
            case TacticResult.COMPLETE:
                assert cur_proof_result.new_proof is not None
                return cur_proof_result.new_proof, last_proof_script
