from __future__ import annotations
from typing import Optional, Any
import random
from dataclasses import dataclass
import math
import time

from coqpyt.coq.lsp.structs import Goal

from data_management.dataset_file import DatasetFile, Proof
from tactic_gen.lm_example import GPTProofFormatter, ProofRetrievalFormatter, LmExample

from model_deployment.model_result import ModelResult, filter_recs
from model_deployment.mine_goals import GoalRecord
from model_deployment.goal_comparer import GoalScorer, AlphaGoalComparer
from model_deployment.proof_manager import ProofManager, TacticResult
from model_deployment.tactic_gen_client import TacticGenClient


@dataclass
class MCTSSuccess:
    time: float
    model_time: float
    successful_proof: Proof
    mcts_root_node: MCTSNode


@dataclass
class MCTSFailure:
    time: float
    model_time: float
    mcts_root_node: MCTSNode


class MCTSNode:
    def __init__(
        self,
        valid: bool,
        makes_progress: bool,
        proof: Proof | None,
        goal_record: GoalRecord | None,
        goals: Optional[list[Goal]],
    ):
        self.valid = valid
        self.makes_progress = makes_progress
        self.proof = proof
        self.goal_record = goal_record
        self.goals = goals
        self.num_visits = 0
        self.total_score = 0.0
        self.children: list[MCTSNode] = []

    def __repr__(self) -> str:
        return f"MCTS Node; valid: {self.valid}; progress: {self.makes_progress}; avg: {self.total_score / self.num_visits if 0 < self.num_visits else 0}; visits: {self.num_visits}"

    def select(self) -> Optional[list[MCTSNode]]:
        if len(self.children) == 0:
            return [self]
        assert 0 < len(self.children)
        best_child_path_and_uct: Optional[tuple[list[MCTSNode], float]] = None
        for c in self.children:
            if not (c.valid and c.makes_progress):
                continue
            if c.num_visits == 0:
                c_path = c.select()
                assert c_path is not None
                return [self] + c_path
            avg = self.total_score / self.num_visits
            margin = 2 * math.sqrt(math.log(self.num_visits) / c.num_visits)
            uct = avg + margin
            if best_child_path_and_uct is None:
                c_path = c.select()
                if c_path is not None:
                    best_child_path_and_uct = c_path, uct
            else:
                _, cur_uct = best_child_path_and_uct
                if cur_uct < uct:
                    c_path = c.select()
                    if c_path is not None:
                        best_child_path_and_uct = c_path, uct
        if best_child_path_and_uct is None:
            return None
        best_child_path, _ = best_child_path_and_uct
        return [self] + best_child_path


@dataclass
class MCTSConf:
    ALIAS = "mcts"
    max_branch: int
    depth_limit: int
    timeout: int
    print_proofs: bool
    initial_proof: Optional[str]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> MCTSConf:
        if "initial_proof" not in yaml_data:
            initial_proof = None
        else:
            initial_proof = yaml_data["initial_proof"]
        return cls(
            yaml_data["max_branch"],
            yaml_data["depth_limit"],
            yaml_data["timeout"],
            yaml_data["print_proofs"],
            initial_proof,
        )


class MCTSSearcher:
    def __init__(
        self,
        tactic_client: TacticGenClient,
        proof_manager: ProofManager,
        max_branch: int,
        depth_limit: int,
        timeout: int,
        print_proofs: bool,
        initial_proof: Optional[str] = None,
    ):
        self.tactic_client = tactic_client
        self.proof_manager = proof_manager
        self.max_branch = max_branch
        self.depth_limit = depth_limit
        self.timeout = timeout
        self.print_proofs = print_proofs

        self.stop_early = initial_proof is not None
        if initial_proof is None:
            initial_proof = ""

        self.comparer = AlphaGoalComparer()
        self.total_model_time = 0

        initial_dset_file = proof_manager.get_initial_context()
        if initial_dset_file is None:
            raise ValueError("Could not get initial datasetfile")
        self.file_context = initial_dset_file.file_context
        self.goal_scorer = self.__get_goal_scorer(initial_dset_file)
        self.initial_proof_obj = initial_dset_file.proofs[-1]
        initial_check_result = proof_manager.check_proof(
            initial_proof, self.initial_proof_obj.theorem, self.need_goal_record
        )
        # print(initial_check_result)
        assert initial_check_result.tactic_result == TacticResult.VALID
        assert initial_check_result.current_goals is not None
        assert initial_check_result.new_proof is not None
        initial_validity = True
        initial_makes_progress = True

        self.initial_num_goals = len(initial_check_result.current_goals)
        self.root = MCTSNode(
            initial_validity,
            initial_makes_progress,
            self.initial_proof_obj,
            initial_check_result.goal_record,
            initial_check_result.current_goals,
        )
        self.seen_goals: list[list[Goal]] = []

    def __get_goal_scorer(self, dset_file: DatasetFile) -> GoalScorer:
        avail_lemmmas: list[str] = []
        for p in dset_file.in_file_avail_premises:
            if p.is_lemma_or_axiom():
                avail_lemmmas.append(p.text)
        for p in dset_file.out_of_file_avail_premises:
            if p.is_lemma_or_axiom():
                avail_lemmmas.append(p.text)
        return GoalScorer(avail_lemmmas)

    @classmethod
    def from_conf(
        cls, conf: MCTSConf, tactic_gen_client: TacticGenClient, manager: ProofManager
    ) -> MCTSSearcher:
        return cls(
            tactic_gen_client,
            manager,
            conf.max_branch,
            conf.depth_limit,
            conf.timeout,
            conf.print_proofs,
            conf.initial_proof,
        )

    @property
    def need_goal_record(self):
        return any(
            [
                isinstance(f, GPTProofFormatter | ProofRetrievalFormatter)
                for f in self.tactic_client.formatters
            ]
        )

    def search(self, **kwags: Any) -> MCTSSuccess | MCTSFailure:
        start_time = time.time()
        while True:
            qed_node, keep_going = self.search_step()
            cur_time = time.time()
            ellapsed_time = cur_time - start_time
            if qed_node is not None:
                assert qed_node.proof is not None
                return MCTSSuccess(
                    ellapsed_time, self.total_model_time, qed_node.proof, self.root
                )
            if self.timeout < ellapsed_time or keep_going is False:
                return MCTSFailure(ellapsed_time, self.total_model_time, self.root)

    def search_step(self) -> tuple[Optional[MCTSNode], bool]:
        selected_path = self.root.select()
        if self.print_proofs:
            print("Path:", selected_path)
        if selected_path is None:
            return None, False
        assert 0 < len(selected_path)
        selected_node = selected_path[-1]
        node_children, qed_node = self.expand(selected_node)
        if self.print_proofs:
            print("Num Children:", len(node_children))
        if qed_node is not None:
            return qed_node, False
        selected_node.children = node_children
        rollout_node: Optional[MCTSNode] = None
        for child in selected_node.children:
            if child.valid and child.makes_progress:
                rollout_node = child
                break
        if rollout_node is None:
            assert selected_node.goals is not None
            rollout_score = self.goal_scorer.score_goals(selected_node.goals)
            backprop_path = selected_path
        else:
            rollout_score, qed_node = self.rollout(rollout_node, 0)
            if qed_node is not None:
                return qed_node, False
            backprop_path = selected_path + [rollout_node]
        for node in backprop_path:
            node.total_score += rollout_score
            node.num_visits += 1
        return None, True

    def rollout(
        self, start_node: MCTSNode, depth: int
    ) -> tuple[float, Optional[MCTSNode]]:
        assert start_node.proof is not None
        assert start_node.goals is not None
        dset_file = DatasetFile(self.file_context, [start_node.proof])
        admitted_step = dset_file.proofs[-1].steps[-1]
        proof_script = dset_file.proofs[-1].proof_prefix_to_string(
            admitted_step, include_theorem=False
        )
        examples = [
            self.proof_manager.get_example(f, dset_file, start_node.goal_record)
            for f in self.tactic_client.formatters
        ]
        assert 0 < len(examples)
        example = random.choice(examples)
        start_time = time.time()
        result = self.tactic_client.get_recs(example, 1, proof_script)
        end_time = time.time()
        assert len(result.next_tactic_list) == 1
        next_tactic = result.next_tactic_list[0]
        self.total_model_time += end_time - start_time
        proof_check_result = self.proof_manager.check_proof(
            proof_script + next_tactic, start_node.proof.theorem, self.need_goal_record
        )
        match proof_check_result.tactic_result:
            case TacticResult.INVALID:
                score = self.goal_scorer.score_goals(start_node.goals)
                if self.print_proofs:
                    print(proof_script)
                return score, None
            case TacticResult.VALID:
                assert proof_check_result.current_goals is not None
                assert start_node.goals is not None
                is_redundant = self.comparer.as_hard_as(
                    proof_check_result.current_goals,
                    start_node.goals,
                    self.proof_manager.fast_client,
                    self.proof_manager.file_prefix,
                )
                if self.depth_limit < depth or is_redundant:
                    if self.print_proofs:
                        print(proof_script)
                    score = self.goal_scorer.score_goals(
                        proof_check_result.current_goals
                    )
                    return score, None
                valid = True
                makes_progress = True
                valid_node = MCTSNode(
                    valid,
                    makes_progress,
                    proof_check_result.new_proof,
                    proof_check_result.goal_record,
                    proof_check_result.current_goals,
                )
                return self.rollout(valid_node, depth + 1)
            case TacticResult.COMPLETE:
                valid = True
                makes_progress = True
                complete_node = MCTSNode(
                    valid,
                    makes_progress,
                    proof_check_result.new_proof,
                    proof_check_result.goal_record,
                    proof_check_result.current_goals,
                )
                return 1e9, complete_node

    def get_all_recs(
        self, examples: list[LmExample], current_proof: str
    ) -> ModelResult:
        recs_per_example = self.max_branch // len(examples)
        all_next_tactics: list[str] = []
        all_next_scores: list[float] = []
        all_next_num_tokens: list[int] = []
        for example in examples:
            result = self.tactic_client.get_recs(
                example, recs_per_example, current_proof
            )
            all_next_tactics.extend(result.next_tactic_list)
            all_next_scores.extend(result.score_list)
            all_next_num_tokens.extend(result.num_tokens_list)
        return filter_recs(all_next_tactics, all_next_scores, all_next_num_tokens, [])

    def expand(
        self, selected_node: MCTSNode
    ) -> tuple[list[MCTSNode], Optional[MCTSNode]]:
        assert len(selected_node.children) == 0
        assert selected_node.proof is not None
        dset_file = DatasetFile(self.file_context, [selected_node.proof])
        examples = [
            self.proof_manager.get_example(f, dset_file, selected_node.goal_record)
            for f in self.tactic_client.formatters
        ]
        start_time = time.time()
        admitted_step = dset_file.proofs[-1].steps[-1]
        proof_script = dset_file.proofs[-1].proof_prefix_to_string(
            admitted_step, include_theorem=False
        )
        result = self.get_all_recs(examples, proof_script)
        end_time = time.time()
        self.total_model_time += end_time - start_time

        if self.print_proofs:
            print(proof_script)
        children: list[MCTSNode] = []
        for tactic, _, _ in zip(
            result.next_tactic_list, result.score_list, result.num_tokens_list
        ):
            proof_check_result = self.proof_manager.check_proof(
                proof_script + tactic,
                selected_node.proof.theorem,
                self.need_goal_record,
            )
            match proof_check_result.tactic_result:
                case TacticResult.COMPLETE:
                    valid = True
                    makes_progress = True
                    complete_node = MCTSNode(
                        valid,
                        makes_progress,
                        proof_check_result.new_proof,
                        proof_check_result.goal_record,
                        proof_check_result.current_goals,
                    )
                    children.append(complete_node)
                    return children, complete_node

                case TacticResult.INVALID:
                    valid = False
                    makes_progress = False
                    invalid_node = MCTSNode(
                        valid,
                        makes_progress,
                        proof_check_result.new_proof,
                        proof_check_result.goal_record,
                        proof_check_result.current_goals,
                    )
                    children.append(invalid_node)

                case TacticResult.VALID:
                    valid = True
                    assert proof_check_result.current_goals is not None
                    if (
                        self.stop_early
                        and len(proof_check_result.current_goals)
                        < self.initial_num_goals
                    ):
                        makes_progress = True
                        complete_node = MCTSNode(
                            valid,
                            makes_progress,
                            proof_check_result.new_proof,
                            proof_check_result.goal_record,
                            proof_check_result.current_goals,
                        )
                        children.append(complete_node)
                        return children, complete_node

                    makes_progress = True
                    for seen_goals in self.seen_goals:
                        if self.comparer.as_hard_as(
                            proof_check_result.current_goals,
                            seen_goals,
                            self.proof_manager.fast_client,
                            self.proof_manager.file_prefix,
                        ):
                            makes_progress = False
                            break
                    if makes_progress:
                        self.seen_goals.append(proof_check_result.current_goals)

                    valid_node = MCTSNode(
                        valid,
                        makes_progress,
                        proof_check_result.new_proof,
                        proof_check_result.goal_record,
                        proof_check_result.current_goals,
                    )
                    children.append(valid_node)
        return children, None
