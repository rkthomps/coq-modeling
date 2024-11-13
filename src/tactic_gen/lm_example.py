from __future__ import annotations
from typing import Any, Optional
from pathlib import Path
from dataclasses import dataclass
import functools


from data_management.line_dict import LineDict
from data_management.splits import FileInfo
from data_management.dataset_file import (
    DatasetFile,
    Proof,
    Sentence,
    Goal,
)
from premise_selection.rerank_client import (
    PremiseClient,
    PremiseConf,
    premise_conf_from_yaml,
    premise_client_from_conf,
    premise_conf_update_ips,
    close_premise_client,
)

from proof_retrieval.proof_retriever import (
    ProofRetriever,
    ProofRetrieverConf,
    proof_conf_update_ips,
    proof_retriever_conf_from_yaml,
    proof_retriever_from_conf,
    close_proof_retriever,
)

from util.util import get_basic_logger


GOAL_SEP = "\n[GOAL]\n"


def get_repos_path(file_path: str) -> Path:
    repos_path = Path("")
    hit_repos = False
    for p in Path(file_path).parts:
        if p == "repos":
            hit_repos = True
        if hit_repos:
            repos_path = repos_path / p
    return repos_path


class LmExample:
    def __init__(
        self,
        proof_script: str,
        proof_state: str,
        next_steps: list[str],
        proofs: Optional[list[str]] = None,
        premises: Optional[list[str]] = None,
        file_name: Optional[str] = None,
        proof_idx: Optional[int] = None,
        step_idx: Optional[int] = None,
    ) -> None:
        self.proof_script = proof_script
        self.proof_state = proof_state
        self.next_steps = next_steps
        self.proofs = proofs
        self.premises = premises
        self.file_name = file_name
        self.proof_idx = proof_idx
        self.step_idx = step_idx

    def __hash__(self) -> int:
        next_step_str = "<NEXT_SEP>".join(self.next_steps)
        proof_str = "<PROOF_SEP>".join(self.proofs) if self.proofs is not None else ""
        prem_str = "<PREM_SEP>".join(self.premises) if self.premises is not None else ""
        return hash(
            (
                self.proof_script,
                self.proof_state,
                next_step_str,
                proof_str,
                prem_str,
                self.file_name,
                self.proof_idx,
                self.step_idx,
            )
        )

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, LmExample):
            return False
        return (
            self.proof_script == other.proof_script
            and self.proof_state == other.proof_state
            and self.next_steps == other.next_steps
            and self.proofs == other.proofs
            and self.premises == other.premises
            and self.file_name == other.file_name
            and self.proof_idx == other.proof_idx
            and self.step_idx == other.step_idx
        )

    def to_json(self) -> Any:
        return {
            "proof_script": self.proof_script,
            "proof_state": self.proof_state,
            "next_steps": self.next_steps,
            "proofs": self.proofs,
            "premises": self.premises,
            "file_name": self.file_name,
            "proof_idx": self.proof_idx,
            "step_idx": self.step_idx,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> LmExample:
        # Backward compatability
        if "target" in json_data:
            next_steps = [json_data["target"]]
        else:
            next_steps = json_data["next_steps"]
        proofs = json_data["proofs"] if "proofs" in json_data else None
        premises = json_data["premises"] if "premises" in json_data else None
        file_name = json_data["file_name"] if "file_name" in json_data else None
        proof_idx = json_data["proof_idx"] if "proof_idx" in json_data else None
        step_idx = json_data["step_idx"] if "step_idx" in json_data else None
        return cls(
            json_data["proof_script"],
            json_data["proof_state"],
            next_steps,
            proofs,
            premises,
            file_name,
            proof_idx,
            step_idx,
        )


def fmt_goals(goals: list[Goal]) -> str:
    goal_strings = [goal.to_string() for goal in goals]
    return GOAL_SEP.join(goal_strings)


@dataclass
class GeneralFormatterConf:
    ALIAS = "general"
    premise_client_conf: Optional[PremiseConf]
    proof_retriever_conf: Optional[ProofRetrieverConf]
    num_premises: Optional[int]
    num_proofs: Optional[int]

    def __hash__(self) -> int:
        return hash(str(self))

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> GeneralFormatterConf:
        if "premise" in yaml_data:
            premise_conf = premise_conf_from_yaml(yaml_data["premise"])
            assert "num_premises" in yaml_data
            num_premises = yaml_data["num_premises"]
        else:
            premise_conf = None
            num_premises = None

        if "proof_ret" in yaml_data:
            proof_ret_conf = proof_retriever_conf_from_yaml(yaml_data["proof_ret"])
            assert "num_proofs" in yaml_data
            num_proofs = yaml_data["num_proofs"]
        else:
            proof_ret_conf = None
            num_proofs = None

        return cls(
            premise_conf,
            proof_ret_conf,
            num_premises,
            num_proofs,
        )


class GeneralFormatter:
    def __init__(
        self,
        premise_client: Optional[PremiseClient],
        proof_retriever: Optional[ProofRetriever],
        num_premises: Optional[int],
        num_proofs: Optional[int],
    ):
        self.premise_client = premise_client
        self.proof_retriever = proof_retriever
        self.num_premises = num_premises
        self.num_proofs = num_proofs

    def example_from_step(
        self,
        step_idx: int,
        proof_idx: int,
        dp_obj: DatasetFile,
        training: bool = False,
        **kwargs: Any,
    ) -> LmExample:
        proof = dp_obj.proofs[proof_idx]
        step = proof.steps[step_idx]
        file_repos_path = get_repos_path(dp_obj.file_context.file)
        if self.proof_retriever is not None:
            assert self.num_proofs is not None
            simliar_proofs = self.proof_retriever.get_similar_proofs(
                step_idx,
                proof,
                dp_obj,
                training,
            )[: self.num_proofs]
            similar_proof_strs = [p.proof_text_to_string() for p in simliar_proofs]
        else:
            similar_proof_strs = None

        if self.premise_client is not None:
            assert self.num_premises is not None
            filtered_result = (
                self.premise_client.premise_filter.get_pos_and_avail_premises(
                    step, proof, dp_obj
                )
            )
            relevant_premises = self.premise_client.get_ranked_premises(
                step_idx, proof, dp_obj, filtered_result.avail_premises, training
            )[: self.num_premises]
            relevant_premise_strs = [p.text for p in relevant_premises]
        else:
            relevant_premise_strs = None

        script = proof.proof_prefix_to_string(step)
        goals = fmt_goals(step.goals)
        next_steps = [s.step.text for s in proof.steps[step_idx:]]
        return LmExample(
            script,
            goals,
            next_steps,
            similar_proof_strs,
            relevant_premise_strs,
            str(file_repos_path),
            proof_idx,
            step_idx,
        )

    def close(self):
        if self.proof_retriever is not None:
            close_proof_retriever(self.proof_retriever)

    @classmethod
    def from_conf(cls, conf: GeneralFormatterConf) -> GeneralFormatter:
        if conf.premise_client_conf is not None:
            premise_client = premise_client_from_conf(conf.premise_client_conf)
            assert conf.num_premises is not None
        else:
            premise_client = None

        if conf.proof_retriever_conf is not None:
            assert conf.num_proofs is not None
            proof_retriever = proof_retriever_from_conf(conf.proof_retriever_conf)
        else:
            proof_retriever = None

        return cls(
            premise_client,
            proof_retriever,
            conf.num_premises,
            conf.num_proofs,
        )


FormatterConf = GeneralFormatterConf


def formatter_from_conf(c: FormatterConf) -> LmFormatter:
    match c:
        case GeneralFormatterConf():
            return GeneralFormatter.from_conf(c)


def formatter_update_ips(f: FormatterConf, port_map: dict[int, tuple[str, int]]):
    match f:
        case GeneralFormatterConf():
            if f.premise_client_conf is not None:
                premise_conf_update_ips(f.premise_client_conf, port_map)
            if f.proof_retriever_conf is not None:
                proof_conf_update_ips(f.proof_retriever_conf, port_map)


def formatter_conf_from_yaml(yaml_data: Any) -> FormatterConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case GeneralFormatterConf.ALIAS:
            return GeneralFormatterConf.from_yaml(yaml_data)
        case _:
            raise ValueError("Formatter conf not found: " + attempted_alias)


LmFormatter = GeneralFormatter


def close_lm_formatter(lm_formatter: LmFormatter):
    match lm_formatter:
        case GeneralFormatter():
            if lm_formatter.proof_retriever is not None:
                close_proof_retriever(lm_formatter.proof_retriever)
            if lm_formatter.premise_client is not None:
                close_premise_client(lm_formatter.premise_client)
