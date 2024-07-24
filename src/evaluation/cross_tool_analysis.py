from __future__ import annotations
from typing import Optional, Any
from pathlib import Path
import os
import json


from dataclasses import dataclass

from model_deployment.run_proofs import load_results
from model_deployment.prove import Summary


@dataclass
class NamedEval:
    name: str
    results: list[GeneralResult]

    def get_proof_pairs(self) -> set[ProofPair]:
        return {ProofPair(result.file, result.theorem) for result in self.results}

    def get_successful_results(self) -> list[SuccessfulResult]:
        successes: list[SuccessfulResult] = []
        for result in self.results:
            if result.success:
                assert result.proof is not None
                successes.append(
                    SuccessfulResult(
                        result.file,
                        result.theorem,
                        result.time,
                        result.proof,
                    )
                )
        return successes

    def get_time_points(self) -> list[PlotPoint]:
        successes = self.get_successful_results()
        successes.sort(key=lambda x: x.time)
        return [PlotPoint(s.time, i + 1) for i, s in enumerate(successes)]

    def filter_results(self, pairs: set[ProofPair]) -> NamedEval:
        filtered: list[GeneralResult] = []
        seen_pairs: set[ProofPair] = set()
        for result in self.results:
            key = ProofPair(result.file, result.theorem)
            if key not in seen_pairs:
                if key in pairs:
                    filtered.append(result)
                seen_pairs.add(key)
        return NamedEval(self.name, filtered)


@dataclass
class PlotPoint:
    x: float
    y: float


@dataclass
class TwoEvalSubsets:
    one_only: set[ProofPair]
    two_only: set[ProofPair]
    one_two: set[ProofPair]


def get_two_eval_subsets(
    evals: list[NamedEval], eval1_alias: str, eval2_alias: str
) -> TwoEvalSubsets:
    eval1_list = [e for e in evals if e.name == eval1_alias]
    assert len(eval1_list) == 1
    eval2_list = [e for e in evals if e.name == eval2_alias]
    assert len(eval2_list) == 1

    e1 = eval1_list[0]
    e2 = eval2_list[0]
    e1_successes = set(
        [ProofPair(s.file, s.theorem) for s in e1.get_successful_results()]
    )
    e2_successes = set(
        [ProofPair(s.file, s.theorem) for s in e2.get_successful_results()]
    )

    return TwoEvalSubsets(
        e1_successes - e2_successes,
        e2_successes - e1_successes,
        e1_successes & e2_successes,
    )


@dataclass
class ProofPair:
    file: Path
    theorem: str

    def __hash__(self) -> int:
        return hash((self.file, self.theorem))


def get_mutual_proof_pairs(evals: list[NamedEval]) -> set[ProofPair]:
    assert 0 < len(evals)
    mutual_pairs = evals[0].get_proof_pairs()
    for eval in evals[1:]:
        mutual_pairs &= eval.get_proof_pairs()
    return mutual_pairs


@dataclass
class SuccessfulResult:
    file: Path
    theorem: str
    time: float
    proof: str


@dataclass
class GeneralResult:
    file: Path
    theorem: str
    time: float
    success: bool
    proof: Optional[str]

    @staticmethod
    def normalize_thm(thm: str) -> str:
        return " ".join(thm.strip().split())

    @classmethod
    def from_proverbot_result(cls, result: ProverBotResult) -> GeneralResult:
        return cls(
            result.project / Path(result.file_name),
            cls.normalize_thm(result.thm_str),
            result.time,
            result.success,
            result.proof,
        )

    @staticmethod
    def clean_tactician_path(file_path: Path, proverbot_paths: list[Path]) -> Path:
        assert file_path.parts[0] == "repos"
        # for path in proverbot_paths:
        #     if str(file_path).endswith(str(path)):
        #         return Path(path)
        rel_path = file_path.relative_to("repos")
        if str(rel_path).startswith("coq-community-"):
            return Path(str(rel_path)[(len("coq-community-")) :])
        if str(rel_path).startswith("coq-contribs-"):
            return Path(str(rel_path)[(len("coq-contribs-")) :])
        if str(rel_path).startswith("thery-"):
            return Path(str(rel_path)[(len("thery-")) :])
        return rel_path

    @staticmethod
    def clean_rango_path(file_path: Path, proverbot_paths: list[Path]) -> Path:
        assert list(file_path.parts[:3]) == ["raw-data", "coq-dataset", "repos"]
        # for path in proverbot_paths:
        #     if str(file_path).endswith(str(path)):
        #         return Path(path)
        rel_path = file_path.relative_to("raw-data/coq-dataset/repos")
        if str(rel_path).startswith("coq-community-"):
            return Path(str(rel_path)[(len("coq-community-")) :])
        if str(rel_path).startswith("coq-contribs-"):
            return Path(str(rel_path)[(len("coq-contribs-")) :])
        if str(rel_path).startswith("thery-"):
            return Path(str(rel_path)[(len("thery-")) :])
        return rel_path

    @classmethod
    def from_tacitician_result(
        cls, result: TacticianResult, proverbot_paths: list[Path]
    ) -> GeneralResult:
        return cls(
            cls.clean_tactician_path(Path(result.file_name), proverbot_paths),
            cls.normalize_thm(result.thm_str),
            result.time,
            result.success,
            result.proof,
        )

    @classmethod
    def from_rango_summary(
        cls, result: Summary, proverbot_paths: list[Path]
    ) -> GeneralResult:
        return cls(
            cls.clean_rango_path(result.file, proverbot_paths),
            cls.normalize_thm(result.theorem),
            result.search_time if result.search_time is not None else -1,
            result.success,
            result.proof,
        )


def load_proverbot(path: Path) -> list[GeneralResult]:
    proverbot_results = load_proverbot_results(path)
    return [GeneralResult.from_proverbot_result(result) for result in proverbot_results]


def load_tactician(
    path: Path, proverbot_paths: Optional[list[Path]] = None
) -> list[GeneralResult]:
    if proverbot_paths is None:
        proverbot_paths = []
    tactician_result = load_tactician_results(path)
    return [
        GeneralResult.from_tacitician_result(result, proverbot_paths)
        for result in tactician_result
    ]


def load_rango(
    path: Path, proverbot_paths: Optional[list[Path]] = None
) -> list[GeneralResult]:
    if proverbot_paths is None:
        proverbot_paths = []
    rango_result = load_results(path)
    return [
        GeneralResult.from_rango_summary(result, proverbot_paths)
        for result in rango_result
    ]


def get_unique_files(results: list[GeneralResult]) -> list[Path]:
    return list({result.file for result in results})


@dataclass
class TacticianResult:
    file_name: str
    thm_str: str
    success: bool
    time: float
    proof: Optional[str]

    def clean_path(self, proverbot_paths: list[str]) -> str:
        file_path = Path(self.file_name)
        assert file_path.parts[0] == "repos"
        for path in proverbot_paths:
            if str(file_path).endswith(path):
                return path
        return str(file_path.relative_to("repos"))

    @classmethod
    def from_json(cls, json_data: Any) -> TacticianResult:
        return cls(
            json_data["file"],
            json_data["theorem"],
            json_data["success"],
            json_data["synth_time"],
            json_data["stdout"],
        )


def load_tactician_results(path: Path) -> list[TacticianResult]:
    results: list[TacticianResult] = []
    for result_file in os.listdir(path):
        with (path / result_file).open() as fin:
            result_data = json.load(fin)
            result = TacticianResult.from_json(result_data)
            results.append(result)
    return results


@dataclass
class ProverBotResult:
    project: str
    file_name: str
    thm_str: str
    success: bool
    time: float
    num_steps: int
    proof: Optional[str]

    META_IDX = 0
    META_PROJ_IDX = 0
    META_FILE_IDX = 1
    META_THM_IDX = 3

    PROOF_IDX = 1

    @classmethod
    def proof_from_cmds(cls, commands: list[Any]) -> str:
        tactics = [c["tactic"] for c in commands]
        return "\n".join(tactics)

    @classmethod
    def from_json(cls, json_data: Any) -> ProverBotResult:
        metadata_json = json_data[cls.META_IDX]
        proj = metadata_json[cls.META_PROJ_IDX]
        file = metadata_json[cls.META_FILE_IDX]
        thm = metadata_json[cls.META_THM_IDX]

        proof_json = json_data[cls.PROOF_IDX]
        success = proof_json["status"] == "SUCCESS"
        if (
            not success
            and proof_json["status"] != "INCOMPLETE"
            and proof_json["status"] != "FAILURE"
            and proof_json["status"] != "CRASHED"
        ):
            print(json.dumps(json_data, indent=2))
            exit()
        proof = cls.proof_from_cmds(proof_json["commands"]) if success else None

        time = proof_json["time_taken"]
        steps = proof_json["steps_taken"]
        return cls(proj, file, thm, success, time, steps, proof)


def results_from_file(file_path: Path) -> list[ProverBotResult]:
    file_results: list[ProverBotResult] = []
    with file_path.open() as fin:
        for line in fin:
            line_info = json.loads(line)
            file_results.append(ProverBotResult.from_json(line_info))
    return file_results


def load_proverbot_results(path: Path) -> list[ProverBotResult]:
    results: list[ProverBotResult] = []
    for root, _, files in os.walk(path):
        for file in files:
            if file.endswith("proofs.txt"):
                results.extend(results_from_file(Path(root) / file))
    return results


if __name__ == "__main__":
    root = Path("evaluations/tactician/results-24-07-22")
    print("Loading results")
    load_tactician_results(root)
