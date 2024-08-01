from __future__ import annotations
from typing import Optional, Any
from pathlib import Path
import ipdb
import re
import os
import json
from edist.sed import standard_sed


from dataclasses import dataclass

from model_deployment.run_proofs import load_results
from model_deployment.prove import Summary, StraightLineSummary


def remove_proof_qed(s: str) -> str:
    return s.replace("Proof.", "").replace("Qed.", "")


def proof_length(s: str) -> int:
    s = remove_proof_qed(s)
    tactics = re.split(r"[.;]\s+", s.strip())
    proof_length = len(tactics)
    if 0 == proof_length:
        print(s)
    assert 0 < proof_length
    return len(tactics)


def fair_edist(s1: str, s2: str) -> int:
    s1 = remove_proof_qed(s1)
    s2 = remove_proof_qed(s2)
    return standard_sed(s1, s2)


@dataclass
class NamedEval:
    name: str
    results: list[GeneralResult]

    def get_proof_pairs(self) -> set[ProofPair]:
        return {ProofPair(result.file, result.theorem) for result in self.results}

    def get_successful_results(self, timeout: float = 600) -> list[SuccessfulResult]:
        successes: list[SuccessfulResult] = []
        for result in self.results:
            if result.success and result.time < timeout:
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

    def get_successful_proof_pairs(
        self, timeout: float = 600
    ) -> dict[ProofPair, SuccessfulResult]:
        success_dict: dict[ProofPair, SuccessfulResult] = {}
        for result in self.results:
            if result.success and result.time < timeout:
                assert result.proof is not None
                success_dict[ProofPair(result.file, result.theorem)] = SuccessfulResult(
                    result.file,
                    result.theorem,
                    result.time,
                    result.proof,
                )
        return success_dict

    def get_successful_proofs_in_range(
        self, lower: int, upper: Optional[int]
    ) -> set[ProofPair]:
        pairs: set[ProofPair] = set()
        for r in self.results:
            if r.success:
                assert r.proof is not None
                proof_len = proof_length(r.proof)
                if lower <= proof_len and (upper is None or proof_len <= upper):
                    pairs.add(ProofPair(r.file, r.theorem))
        return pairs

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


def get_mutually_successful_proof_pairs(
    evals: list[NamedEval],
) -> dict[str, list[SuccessfulResult]]:
    assert 0 < len(evals)
    eval_successes = [e.get_successful_proof_pairs() for e in evals]
    all_successes = set(eval_successes[0].keys())
    for e in evals[1:]:
        e_successes = set(e.get_successful_proof_pairs().keys())
        all_successes &= e_successes

    success_dict: dict[str, list[SuccessfulResult]] = dict(
        [(e.name, []) for e in evals]
    )
    for easy_proof in all_successes:
        for e, e_succeses in zip(evals, eval_successes):
            success_dict[e.name].append(e_succeses[easy_proof])
    for k, v in success_dict.items():
        assert len(v) == len(all_successes)
    return success_dict


@dataclass
class SuccessfulResult:
    file: Path
    theorem: str
    time: float
    proof: str


@dataclass
class GeneralResult:
    file: Path
    raw_file: Path
    theorem: str
    time: float
    success: bool
    proof: Optional[str]

    GIT_NAMES = ["coq-community", "coq-contribs", "thery", "AbsInt", "CertiKOS"]

    def to_json(self) -> Any:
        return {
            "file": str(self.file),
            "raw_file": str(self.raw_file),
            "theorem": self.theorem,
            "time": self.time,
            "success": self.success,
            "proof": self.proof,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> GeneralResult:
        return cls(
            Path(json_data["file"]),
            Path(json_data["raw_file"]),
            json_data["theorem"],
            json_data["time"],
            json_data["success"],
            json_data["proof"],
        )

    @classmethod
    def get_tactician_proof(cls, stdout: str) -> str:
        proof_text = re.sub(r"\u001b\[\d+m", "", stdout)
        proof_text = proof_text.replace("only 1: ", "")
        proof_portion_match = re.search(
            r"synth with cache \((.*?)\)\.\r\nNo more (sub)?goals.", proof_text
        )
        assert proof_portion_match is not None
        (proof_portion, _) = proof_portion_match.groups()
        return proof_portion

    @staticmethod
    def normalize_thm(thm: str) -> str:
        return " ".join(thm.strip().split())

    @classmethod
    def from_proverbot_result(cls, result: ProverBotResult) -> GeneralResult:
        return cls(
            cls.clean_proverbot_path(result.project / Path(result.file_name)),
            result.project / Path(result.file_name),
            cls.normalize_thm(result.thm_str),
            result.time,
            result.success,
            result.proof,
        )

    @staticmethod
    def clean_proverbot_path(file_path: Path) -> Path:
        return Path(file_path.parts[0]) / file_path.name

    @classmethod
    def strip_path(cls, path: Path) -> Path:
        for name in cls.GIT_NAMES:
            dashed_name = f"{name}-"
            if str(path).startswith(dashed_name):
                return Path(str(path)[len(dashed_name) :])
        raise ValueError(f"Unexpected prefix {path}")

    @classmethod
    def clean_tactician_path(cls, file_path: Path) -> Path:
        assert file_path.parts[0] == "repos"
        rel_path = file_path.relative_to("repos")
        stripped_path = cls.strip_path(rel_path)
        return Path(stripped_path.parts[0]) / stripped_path.name

    @classmethod
    def clean_rango_path(cls, file_path: Path) -> Path:
        assert list(file_path.parts[:3]) == ["raw-data", "coq-dataset", "repos"]
        rel_path = file_path.relative_to("raw-data/coq-dataset/repos")
        stripped_path = cls.strip_path(rel_path)
        return Path(stripped_path.parts[0]) / stripped_path.name

    @classmethod
    def from_tacitician_result(cls, result: TacticianResult) -> GeneralResult:
        return cls(
            cls.clean_tactician_path(Path(result.file_name)),
            Path(result.file_name),
            cls.normalize_thm(result.thm_str),
            result.time,
            result.success,
            (
                cls.get_tactician_proof(result.proof)
                if result.success and result.proof is not None
                else None
            ),
        )

    @classmethod
    def from_rango_summary(cls, result: Summary) -> GeneralResult:
        assert isinstance(result, StraightLineSummary)
        proof = None
        if result.success:
            assert result.attempts is not None
            assert result.proof is not None
            assert result.attempts[-1] in result.proof
            proof = result.attempts[-1]
        return cls(
            cls.clean_rango_path(result.file),
            result.file.relative_to("raw-data/coq-dataset"),
            cls.normalize_thm(result.theorem),
            result.search_time if result.search_time is not None else -1,
            result.success,
            proof,
        )


def load_human(path: Path) -> list[GeneralResult]:
    human_results: list[GeneralResult] = []
    for human_result in os.listdir(path):
        with (path / human_result).open() as fin:
            human_data = json.load(fin)
            human_result = GeneralResult.from_json(human_data)
            human_result.theorem = GeneralResult.normalize_thm(human_result.theorem)
            human_result.file = (
                Path(human_result.file.parts[0]) / human_result.file.name
            )
            human_results.append(human_result)
    return human_results


def load_proverbot(path: Path) -> list[GeneralResult]:
    proverbot_results = load_proverbot_results(path)
    return [GeneralResult.from_proverbot_result(result) for result in proverbot_results]


def load_tactician(path: Path) -> list[GeneralResult]:
    tactician_results = load_tactician_results(path)
    return [GeneralResult.from_tacitician_result(r) for r in tactician_results]


def load_rango(path: Path) -> list[GeneralResult]:
    rango_result = load_results(path)
    return [
        GeneralResult.from_rango_summary(result)
        for result in rango_result
        if result.search_time is not None
    ]


def get_unique_files(results: list[GeneralResult]) -> list[Path]:
    return list({result.file for result in results})


@dataclass
class TacticianResult:
    file_name: str
    thm_str: str
    success: bool
    time: float
    timeout: bool
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
            json_data["timeout"],
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
    # root = Path("evaluations/tactician/results-24-07-22")
    root = Path("evaluations/graph2tac/results-2024-07-29")
    print("Loading results")
    # results, files = load_tactician_results(root)
    results = load_tactician_results(root)
    problems: list[Any] = []
    for r in results:
        if r.success:
            assert r.proof is not None
            GeneralResult.get_tactician_proof(r.proof)
            # try:
            #     GeneralResult.get_tactician_proof(r.proof)
            # except AssertionError:
            #     problems.append(
            #         {
            #             "file": r.file_name,
            #             "result_file": file,
            #             "stdout": r.proof,
            #         }
            #     )
    # print(f"{len(problems)} problems found")
    # with open("g2t_problems.json", "w") as fout:
    #     fout.write(json.dumps(problems, indent=2))
