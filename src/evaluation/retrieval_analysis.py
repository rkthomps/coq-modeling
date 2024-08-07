from __future__ import annotations
import os
import json
from tqdm import tqdm
import argparse
from typing import Any, Optional
from pathlib import Path
from enum import Enum
from dataclasses import dataclass

from data_management.sentence_db import SentenceDB
from data_management.dataset_file import (
    DatasetFile,
    Proof,
    Sentence,
    Term,
    Goal as DpGoal,
)
from data_management.splits import FileInfo, info_from_path, Split
from model_deployment.rerank_client import PremiseClient
from premise_selection.premise_client import TFIdfClient
from premise_selection.premise_formatter import BasicPremiseFormat, BasicContextFormat
from premise_selection.premise_filter import NO_COQ_LEMMA_FILTER
from model_deployment.prove import get_proof_info, normalize
from model_deployment.proof_manager import ProofManager, TacticResult
from proof_retrieval.proof_retriever import ProofRetriever, TfIdfProofRetriever
from evaluation.cross_tool_analysis import (
    GeneralResult,
    load_proverbot,
    load_tactician,
    load_rango,
)

from tactic_gen.tactic_data import ProofPremiseCollator, whole_number_allocate
from transformers import PreTrainedTokenizer, AutoTokenizer

from coqpyt.coq.structs import TermType, Step as CStep
from coqpyt.lsp.structs import TextDocumentIdentifier
from coqpyt.coq.lsp.structs import GoalAnswer, Goal
from util.util import get_fresh_path, get_basic_logger

import ipdb

_logger = get_basic_logger(__name__)


@dataclass
class RetrievalProofAttemptStep:
    retrieved_proofs: list[Proof]
    retrieved_lemmas: list[Sentence]

    def show_proofs(self):
        for p in self.retrieved_proofs:
            print(p.proof_text_to_string())
            print()

    def show_lemmas(self):
        for l in self.retrieved_lemmas:
            print(l.text)
            print()

    def to_json(self, sentence_db: SentenceDB) -> Any:
        return {
            "retrieved_proofs": [
                p.to_json(sentence_db, False) for p in self.retrieved_proofs
            ],
            "retrieved_lemmas": [
                l.to_json(sentence_db, False) for l in self.retrieved_lemmas
            ],
        }

    @classmethod
    def from_json(
        cls, json_data: Any, sentence_db: SentenceDB
    ) -> RetrievalProofAttemptStep:
        return cls(
            [Proof.from_json(p, sentence_db) for p in json_data["retrieved_proofs"]],
            [Sentence.from_json(l, sentence_db) for l in json_data["retrieved_lemmas"]],
        )


@dataclass
class RetrievalProofAttempt:
    thm: str
    proof_steps: list[str]
    retrieval_steps: list[RetrievalProofAttemptStep]
    proof_idx: int
    dp_name: str

    def get_save_name(self) -> str:
        return f"{self.dp_name}-{self.proof_idx}"[(-255):]

    def to_json(self, sentence_db: SentenceDB) -> Any:
        return {
            "thm": self.thm,
            "proof_steps": self.proof_steps,
            "retrieval_steps": [s.to_json(sentence_db) for s in self.retrieval_steps],
            "proof_idx": self.proof_idx,
            "dp_name": self.dp_name,
        }

    @classmethod
    def from_json(
        cls, json_data: Any, sentence_db: SentenceDB
    ) -> RetrievalProofAttempt:
        return cls(
            json_data["thm"],
            json_data["proof_steps"],
            [
                RetrievalProofAttemptStep.from_json(s, sentence_db)
                for s in json_data["retrieval_steps"]
            ],
            json_data["proof_idx"],
            json_data["dp_name"],
        )

    @classmethod
    def load(cls, path: Path, sentence_db: SentenceDB) -> RetrievalProofAttempt:
        with path.open("r") as fin:
            return cls.from_json(json.load(fin), sentence_db)


def get_proof_attempt(
    proof_idx: int,
    proof: Proof,
    dset_file: DatasetFile,
    file_info: FileInfo,
    proof_retriever: ProofRetriever,
    premise_retriever: PremiseClient,
    collator: ProofPremiseCollator,
    tokenizer: PreTrainedTokenizer,
) -> RetrievalProofAttempt:
    proof_steps: list[str] = []
    retrieval_steps: list[RetrievalProofAttemptStep] = []
    for i, step in enumerate(proof.steps):
        proof_steps.append(step.step.text)
        retrieved_proofs = proof_retriever.get_similar_proofs(
            i,
            proof,
            dset_file,
            file_info=file_info,
        )
        proof_strs = [p.proof_text_to_string() for p in retrieved_proofs]
        num_proofs = len(
            whole_number_allocate(tokenizer, proof_strs, collator.proof_tokens)
        )
        proofs = retrieved_proofs[:num_proofs]

        filter_result = premise_retriever.premise_filter.get_pos_and_avail_premises(
            step, proof, dset_file
        )
        retrieved_premises = premise_retriever.get_ranked_premise_generator(
            step, proof, dset_file, filter_result.avail_premises
        )

        premise_strs = [
            premise_retriever.premise_format.format(s)
            for s in list(retrieved_premises)[:50]
        ]
        num_premises = len(
            whole_number_allocate(tokenizer, premise_strs, collator.premise_tokens)
        )
        premises = list(retrieved_premises)[:num_premises]
        retrieval_steps.append(RetrievalProofAttemptStep(proofs, premises))
    assert len(proof_steps) == len(retrieval_steps)
    return RetrievalProofAttempt(
        proof.theorem.term.text,
        proof_steps,
        retrieval_steps,
        proof_idx,
        file_info.dp_name,
    )


def get_goals(
    thm_step: CStep, proof_steps: list[CStep], proof_manager: ProofManager
) -> list[list[DpGoal]]:
    prev_pos = thm_step.ast.range.end
    step_goals: list[list[DpGoal]] = []
    for step in proof_steps:
        goal_answer = proof_manager.fast_client.client.proof_goals(
            TextDocumentIdentifier(proof_manager.fast_client.file_uri), prev_pos
        )
        prev_pos = step.ast.range.end
        assert goal_answer is not None
        assert goal_answer.goals is not None
        goals = [DpGoal.from_json(repr(g)) for g in goal_answer.goals.goals]
        step_goals.append(goals)
    assert len(step_goals) == len(proof_steps)
    return step_goals


def get_retrieval_proof_attempt(
    proof_retriever: ProofRetriever,
    premise_retriever: PremiseClient,
    collator: ProofPremiseCollator,
    tokenizer: PreTrainedTokenizer,
    file: Path,
    workspace: Path,
    thm: str,
    proof: str,
    data_loc: Path,
    sentence_db: SentenceDB,
) -> tuple[RetrievalProofAttempt, RetrievalProofAttempt]:
    thm_term = Term.from_text(thm, TermType.THEOREM)
    file_info = info_from_path(file, workspace, data_loc)
    file_dp = file_info.get_dp(data_loc, sentence_db)
    occurance_num = 0
    human_proof_idx: Optional[int] = None
    human_proof: Optional[Proof] = None
    machine_proof_idx: Optional[int] = None
    machine_proof: Optional[Proof] = None
    prev_proofs: Optional[list[Proof]] = None
    while True:
        human_proof = None
        human_proof_idx = None
        prev_proofs = None
        matches = 0
        for i, dp_proof in enumerate(file_dp.proofs):
            if normalize(thm) in normalize(dp_proof.theorem.term.text):
                if matches == occurance_num:
                    human_proof_idx = i
                    human_proof = dp_proof
                    prev_proofs = file_dp.proofs[:i]
                    break
                else:
                    matches += 1

        assert human_proof is not None
        assert human_proof_idx is not None
        assert prev_proofs is not None

        proof_info = get_proof_info(data_loc, file_info, thm_term, occurance_num)

        with ProofManager(
            file_dp.file_context,
            prev_proofs,
            proof_info,
            file_info,
            sentence_db,
            Split.TEST,
            data_loc,
        ) as proof_manager:
            check_result = proof_manager.check_proof(
                proof, human_proof.theorem, need_goal_record=False
            )
            match check_result.tactic_result:
                case TacticResult.COMPLETE:
                    assert check_result.new_proof is not None
                    assert check_result.steps is not None
                    thm_step = check_result.steps[proof_manager.proof_info.proof_point]
                    proof_start_step = proof_manager.proof_info.proof_point + 1
                    proof_end_step = proof_start_step + len(
                        check_result.new_proof.steps
                    )
                    machine_proof = check_result.new_proof
                    machine_proof_idx = len(prev_proofs)
                    machine_proof_goals = get_goals(
                        thm_step,
                        check_result.steps[proof_start_step:proof_end_step],
                        proof_manager,
                    )
                    assert len(machine_proof_goals) == len(machine_proof.steps)
                    for g, s in zip(machine_proof_goals, machine_proof.steps):
                        s.goals = g
                    break
                case _:
                    occurance_num += 1

    assert human_proof is not None
    assert human_proof_idx is not None
    assert machine_proof is not None
    assert machine_proof_idx is not None
    assert prev_proofs is not None
    human_retrieval_attempt = get_proof_attempt(
        human_proof_idx,
        human_proof,
        file_dp,
        file_info,
        proof_retriever,
        premise_retriever,
        collator,
        tokenizer,
    )

    machine_dp = DatasetFile(file_dp.file_context, prev_proofs + [machine_proof])
    machine_retrieval_attempt = get_proof_attempt(
        machine_proof_idx,
        machine_proof,
        machine_dp,
        file_info,
        proof_retriever,
        premise_retriever,
        collator,
        tokenizer,
    )
    return human_retrieval_attempt, machine_retrieval_attempt


class EvalType(Enum):
    RANGO = 1
    PROVERBOT = 2
    TACTICIAN = 3

    @classmethod
    def from_str(cls, s: str) -> EvalType:
        match s:
            case "rango":
                return cls.RANGO
            case "proverbot":
                return cls.PROVERBOT
            case "tactician":
                return cls.TACTICIAN
            case _:
                raise ValueError(f"Invalid eval type: {s}")


DATA_LOC = Path("raw-data/coq-dataset")
SENTENCE_DB_LOC = Path("raw-data/coq-dataset/sentences.db")
HUMAN_EVAL_NAME = "human"
MACHINE_EVAL_NAME = "machine"


def check_if_exists(
    save_loc: Path, eval: GeneralResult, file_info: FileInfo, sentence_db: SentenceDB
) -> bool:
    for result_name in os.listdir(save_loc / MACHINE_EVAL_NAME):
        if not result_name.startswith(file_info.dp_name):
            continue
        result = RetrievalProofAttempt.load(
            save_loc / MACHINE_EVAL_NAME / result_name, sentence_db
        )
        result_proof = " ".join(result.proof_steps)
        proof_good = eval.proof is not None and eval.proof in result_proof
        thm_good = normalize(eval.theorem) in normalize(result.thm)
        human_exists = (save_loc / HUMAN_EVAL_NAME / result_name).exists()
        print(proof_good, thm_good, human_exists)
        if proof_good and thm_good and human_exists:
            return True
    return False


def collect_retrieved_items(eval_root: Path, eval_type: EvalType, save_root: Path):
    # HARD CODED A LOT OF THINGS
    sentence_db = SentenceDB.load(SENTENCE_DB_LOC)
    proof_retriever = TfIdfProofRetriever(20, DATA_LOC, sentence_db)
    proof_prem_collator = ProofPremiseCollator(512, 1024, 1024, 514, 128, False)
    premise_retriever = TFIdfClient(
        BasicContextFormat, BasicPremiseFormat, NO_COQ_LEMMA_FILTER
    )
    model_name = "deepseek-ai/deepseek-coder-1.3b-instruct"
    tokenizer = AutoTokenizer.from_pretrained(model_name)

    match eval_type:
        case EvalType.RANGO:
            evals = load_rango(eval_root)
        case EvalType.PROVERBOT:
            evals = load_proverbot(eval_root)
        case EvalType.TACTICIAN:
            evals = load_tactician(eval_root)

    os.makedirs(save_root / HUMAN_EVAL_NAME, exist_ok=True)
    os.makedirs(save_root / MACHINE_EVAL_NAME, exist_ok=True)

    for eval in tqdm(evals):
        if not eval.success:
            continue
        assert eval.proof is not None
        eval_file_loc = DATA_LOC / eval.raw_file
        assert eval_file_loc.exists()
        workspace_loc = DATA_LOC / eval_file_loc.relative_to(DATA_LOC).parts[0]

        file_info = info_from_path(eval_file_loc, workspace_loc, DATA_LOC)
        if check_if_exists(save_root, eval, file_info, sentence_db):
            _logger.info(f"Skipping {eval.theorem} in {file_info.dp_name}. Exists")

        human_retrieval_attempt, machine_retrieval_attempt = (
            get_retrieval_proof_attempt(
                proof_retriever,
                premise_retriever,
                proof_prem_collator,
                tokenizer,
                eval_file_loc,
                workspace_loc,
                eval.theorem,
                eval.proof,
                DATA_LOC,
                sentence_db,
            )
        )

        human_save_loc = (
            save_root / HUMAN_EVAL_NAME / human_retrieval_attempt.get_save_name()
        )
        with human_save_loc.open("w") as fout:
            fout.write(json.dumps(human_retrieval_attempt.to_json(sentence_db)))

        machine_save_loc = (
            save_root / MACHINE_EVAL_NAME / machine_retrieval_attempt.get_save_name()
        )
        with machine_save_loc.open("w") as fout:
            fout.write(json.dumps(machine_retrieval_attempt.to_json(sentence_db)))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("eval_root", help="Location of the evaluation")
    parser.add_argument("eval_type", help="'tactician', 'rango', or 'proverbot'")
    parser.add_argument("save_root", help="Root to save the evaluation")
    args = parser.parse_args()

    os.environ["TOKENIZERS_PARALLELISM"] = "false"
    eval_root = Path(args.eval_root)
    eval_type = EvalType.from_str(args.eval_type)
    save_root = Path(args.save_root)

    collect_retrieved_items(eval_root, eval_type, save_root)

    # data_loc = Path("raw-data/coq-dataset")
    # sentence_db_loc = Path("raw-data/coq-dataset/sentences.db")
    # sentence_db = SentenceDB.load(sentence_db_loc)
    # proof_retriever = TfIdfProofRetriever(20, data_loc, sentence_db)
    # proof_prem_collator = ProofPremiseCollator(512, 1024, 1024, 514, 128, False)
    # premise_retriever = TFIdfClient(
    #     BasicContextFormat, BasicPremiseFormat, NO_COQ_LEMMA_FILTER
    # )
    # model_name = "deepseek-ai/deepseek-coder-1.3b-instruct"
    # tokenizer = AutoTokenizer.from_pretrained(model_name)

    # file = Path("raw-data/coq-dataset/repos/AbsInt-CompCert/aarch64/Archi.v")
    # workspace = Path("raw-data/coq-dataset/repos/AbsInt-CompCert")
    # proof = "\nProof.\n  intros. destruct n as [s p]; unfold choose_nan_64; simpl.\n  rewrite choose_nan_idem.\n  auto."
    # theorem = "Lemma choose_nan_64_idem: forall n, choose_nan_64 (n :: n :: nil) = choose_nan_64 (n :: nil)."

    # human_retrieval_attempt, machine_retrieval_attempt = get_retrieval_proof_attempt(
    #     proof_retriever,
    #     premise_retriever,
    #     proof_prem_collator,
    #     tokenizer,
    #     file,
    #     workspace,
    #     theorem,
    #     proof,
    #     data_loc,
    #     sentence_db,
    # )

    # ipdb.set_trace()
