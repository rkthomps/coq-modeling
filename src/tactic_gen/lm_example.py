from __future__ import annotations
from typing import Any, Optional
from pathlib import Path
from dataclasses import dataclass
import functools


from data_management.prev_lines import LineDict
from data_management.splits import FileInfo
from data_management.dataset_file import (
    DatasetFile,
    Proof,
    Sentence,
    Goal,
)
from tactic_gen.n_step_sampler import (
    NStepSampler,
    NStepConf,
    n_step_conf_from_yaml,
    n_step_from_conf,
)
from model_deployment.rerank_client import (
    PremiseClient,
    PremiseConf,
    premise_conf_from_yaml,
    premise_client_from_conf,
    premise_conf_update_ips,
    merge_premise_confs,
    close_premise_client,
)

from proof_retrieval.proof_retriever import TextProofRetriever, TextProofRetrieverConf

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


GOAL_SEP = "\n[GOAL]\n"


class LmExample:
    def __init__(
        self,
        proof_script: str,
        proof_state: str,
        next_steps: list[str],
        proofs: Optional[list[str]] = None,
        premises: Optional[list[str]] = None,
        prev_lines: Optional[list[str]] = None,
    ) -> None:
        self.proof_script = proof_script
        self.proof_state = proof_state
        self.next_steps = next_steps
        self.proofs = proofs
        self.premises = premises
        self.prev_lines = prev_lines

    def to_json(self) -> Any:
        return {
            "proof_script": self.proof_script,
            "proof_state": self.proof_state,
            "next_steps": self.next_steps,
            "proofs": self.proofs,
            "premises": self.premises,
            "prev_lines": self.prev_lines,
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
        prev_lines = json_data["prev_lines"] if "prev_lines" in json_data else None
        return cls(
            json_data["proof_script"],
            json_data["proof_state"],
            next_steps,
            proofs,
            premises,
            prev_lines,
        )


def fmt_goals(goals: list[Goal]) -> str:
    goal_strings = [goal.to_string() for goal in goals]
    return GOAL_SEP.join(goal_strings)


@dataclass
class GeneralFormatterConf:
    ALIAS = "general"
    premise_client_conf: Optional[PremiseConf]
    proof_retriever_conf: Optional[TextProofRetrieverConf]
    num_premises: Optional[int]
    num_proofs: Optional[int]

    def __hash__(self) -> int:
        return hash(str(self))

    def merge(self, other: GeneralFormatterConf) -> GeneralFormatterConf:
        if self.premise_client_conf is None:
            return GeneralFormatterConf(
                self.premise_client_conf,
                self.proof_retriever_conf,
                self.num_premises,
                self.num_proofs,
            )
        assert other.premise_client_conf is not None
        new_premise_client = merge_premise_confs(
            self.premise_client_conf, other.premise_client_conf
        )
        return GeneralFormatterConf(
            new_premise_client,
            self.proof_retriever_conf,
            self.num_premises,
            self.num_proofs,
        )

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
            proof_ret_conf = TextProofRetrieverConf.from_yaml(yaml_data["proof_ret"])
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
        proof_retriever: Optional[TextProofRetriever],
        num_premises: Optional[int],
        num_proofs: Optional[int],
    ):
        self.premise_client = premise_client
        self.proof_retriever = proof_retriever
        self.num_premises = num_premises
        self.num_proofs = num_proofs

    def example_from_step(
        self, step_idx: int, proof_idx: int, dp_obj: DatasetFile, **kwargs: Any
    ) -> LmExample:
        proof = dp_obj.proofs[proof_idx]
        step = proof.steps[step_idx]
        if self.proof_retriever is not None:
            assert self.num_proofs is not None
            simliar_proofs = self.proof_retriever.get_similar_proofs(
                step, proof, dp_obj
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
            relevant_premises = list(
                self.premise_client.get_ranked_premise_generator(
                    step, proof, dp_obj, filtered_result.avail_premises
                )
            )[: self.num_premises]
            relevant_premise_strs = [p.text for p in relevant_premises]
        else:
            relevant_premise_strs = None

        script = proof.proof_prefix_to_string(step)
        goals = fmt_goals(step.goals)
        next_steps = [s.step.text for s in proof.steps[step_idx:]]
        return LmExample(
            script, goals, next_steps, similar_proof_strs, relevant_premise_strs
        )

    def close(self):
        if self.proof_retriever is not None:
            self.proof_retriever.close()

    @classmethod
    def from_conf(cls, conf: GeneralFormatterConf) -> GeneralFormatter:
        if conf.premise_client_conf is not None:
            premise_client = premise_client_from_conf(conf.premise_client_conf)
            assert conf.num_premises is not None
        else:
            premise_client = None

        if conf.proof_retriever_conf is not None:
            assert conf.num_proofs is not None
            proof_retriever = TextProofRetriever.from_conf(conf.proof_retriever_conf)
        else:
            proof_retriever = None

        return cls(
            premise_client,
            proof_retriever,
            conf.num_premises,
            conf.num_proofs,
        )


@dataclass
class PrevLineFormatterConf:
    ALIAS = "prev-line"
    data_loc: Path
    line_dict_loc: Path

    def __hash__(self) -> int:
        return hash(str(self))

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> PrevLineFormatterConf:
        return cls(Path(yaml_data["data_loc"]), Path(yaml_data["line_dict_loc"]))


@functools.lru_cache(maxsize=128)
def get_file_lines(file: Path) -> list[str]:
    with file.open("r") as f:
        return f.read().split("\n")


class PrevLineFormatter:
    def __init__(self, data_loc: Path, line_dict: LineDict):
        self.data_loc = data_loc
        self.line_dict = line_dict

    def get_repos_path(self, file_path: str) -> Path:
        repos_path = Path("")
        hit_repos = False
        for p in Path(file_path).parts:
            if p == "repos":
                hit_repos = True
            if hit_repos:
                repos_path = repos_path / p
        return repos_path

    def example_from_step(
        self, step_idx: int, proof_idx: int, dp_obj: DatasetFile, **kwargs: Any
    ) -> LmExample:
        proof = dp_obj.proofs[proof_idx]
        step = proof.steps[step_idx]
        file_repos_path = self.get_repos_path(dp_obj.file_context.file)

        file_loc = self.data_loc / file_repos_path
        file_lines = get_file_lines(file_loc)

        if self.line_dict.has_file(str(file_repos_path)):
            prefix_lines = file_lines[
                : self.line_dict.get(str(file_repos_path), proof_idx)
            ]
        else:
            prefix_lines = []

        script = proof.proof_prefix_to_string(step)
        goals = fmt_goals(step.goals)
        next_steps = [s.step.text for s in proof.steps[step_idx:]]
        return LmExample(script, goals, next_steps, None, None, prefix_lines)

    @classmethod
    def from_conf(cls, conf: PrevLineFormatterConf) -> PrevLineFormatter:
        line_dict = LineDict.load(conf.line_dict_loc)
        return cls(conf.data_loc, line_dict)


FormatterConf = GeneralFormatterConf | PrevLineFormatterConf


def formatter_from_conf(c: FormatterConf) -> LmFormatter:
    match c:
        case GeneralFormatterConf():
            return GeneralFormatter.from_conf(c)
        case PrevLineFormatterConf():
            return PrevLineFormatter.from_conf(c)


def formatter_update_ips(f: FormatterConf, port_map: dict[int, tuple[str, int]]):
    match f:
        case GeneralFormatterConf():
            if f.premise_client_conf is not None:
                premise_conf_update_ips(f.premise_client_conf, port_map)


def merge_formatters(f1: FormatterConf, f2: FormatterConf) -> FormatterConf:
    match f1:
        case GeneralFormatterConf():
            assert isinstance(f2, GeneralFormatterConf)
            return f1.merge(f2)
        case PrevLineFormatterConf():
            assert isinstance(f2, PrevLineFormatterConf)
            assert f1 == f2
            return f1


def formatter_conf_from_yaml(yaml_data: Any) -> FormatterConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case GeneralFormatterConf.ALIAS:
            return GeneralFormatterConf.from_yaml(yaml_data)
        case PrevLineFormatterConf.ALIAS:
            return PrevLineFormatterConf.from_yaml(yaml_data)
        case _:
            raise ValueError("Formatter conf not found: " + attempted_alias)


LmFormatter = GeneralFormatter | PrevLineFormatter


def close_lm_formatter(lm_formatter: LmFormatter):
    match lm_formatter:
        case GeneralFormatter():
            if lm_formatter.proof_retriever is not None:
                lm_formatter.proof_retriever.close()
            if lm_formatter.premise_client is not None:
                close_premise_client(lm_formatter.premise_client)
