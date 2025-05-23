from __future__ import annotations
from typing import Optional, Any
from pathlib import Path
import ipdb
import re
import os
import json
from edist.sed import standard_sed


from dataclasses import dataclass

from data_management.dataset_file import DatasetFile
from data_management.splits import DATA_POINTS_NAME, REPOS_NAME
from data_management.sentence_db import SentenceDB
from model_deployment.prove import Summary, StraightLineSummary, load_results


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


@dataclass(unsafe_hash=True)
class CacheKey:
    data_loc: Path
    dp_name: str
    proof_idx: int


# @dataclass(frozen=True)
# class ProofDesc:
#     file: Path
#     theorem: str
#     module: str

#     def __lt__(self, other: ProofDesc) -> bool:
#         return (self.file, self.theorem, self.module) < (other.file, other.theorem, other.module)


def kill_comments(string: str) -> str:
    """
    From https://github.com/HazardousPeach/coq_serapy/blob/0fc951116a8ccbc4dd1c701f160209cd98a54d78/src/coq_serapy/coq_util.py#L19
    """
    result = ""
    depth = 0
    in_quote = False
    for i in range(len(string)):
        if in_quote:
            if depth == 0:
                result += string[i]
            if string[i] == '"' and string[i - 1] != "\\":
                in_quote = False
        else:
            if string[i : i + 2] == "(*":
                depth += 1
            if depth == 0:
                result += string[i]
            if string[i - 1 : i + 1] == "*)" and depth > 0:
                depth -= 1
            if string[i] == '"' and string[i - 1] != "\\":
                in_quote = True
    return result


@dataclass
class NamedEval:
    name: str
    results: list[GeneralResult]

    # def get_non_duplicate_proof_descs(self) -> set[ProofDesc]:
    #     duplicates = set()
    #     non_duplicates = set()
    #     for r in self.results:
    #         desc = r.get_desc()
    #         if desc in duplicates:
    #             continue
    #         if desc in non_duplicates:
    #             duplicates.add(desc)
    #             non_duplicates.remove(desc)
    #         else:
    #             non_duplicates.add(desc)
    #     return non_duplicates

    # def filter_descs(self, descs: set[ProofDesc]) -> NamedEval:
    #     filtered: list[GeneralResult] = []
    #     seen_descs: set[ProofDesc] = set()
    #     for result in self.results:
    #         desc = result.get_desc()
    #         assert desc not in seen_descs
    #         if desc in descs:
    #             filtered.append(result)
    #         seen_descs.add(desc)
    #     return NamedEval(self.name, filtered)

    def get_non_duplicate_proof_pairs(self) -> set[ProofPair]:
        duplicates = set()
        non_duplicates = set()
        for r in self.results:
            pair = ProofPair(r.file, r.theorem)
            if pair in duplicates:
                continue
            if pair in non_duplicates:
                duplicates.add(pair)
                non_duplicates.remove(pair)
            else:
                non_duplicates.add(pair)
        return non_duplicates

    def get_indexed_proof_pairs(self) -> set[IndexedProofPair]:
        indexed_pairs: set[IndexedProofPair] = set()
        for result in self.results:
            assert result.file_idx is not None
            indexed_pairs.add(
                IndexedProofPair(result.file, result.theorem, result.file_idx)
            )
        return indexed_pairs

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

    def get_proofs_in_dep_range(
        self, lower: int, upper: Optional[int], proj: bool = False
    ) -> set[ProofPair]:
        pairs: set[ProofPair] = set()
        for r in self.results:
            assert r.num_deps is not None
            assert r.num_proj_deps is not None
            num_deps = r.num_proj_deps if proj else r.num_deps
            if lower <= num_deps and (upper is None or num_deps <= upper):
                pairs.add(ProofPair(r.file, r.theorem))
        return pairs

    def get_time_points(self) -> list[PlotPoint]:
        successes = self.get_successful_results()
        successes.sort(key=lambda x: x.time)
        return [PlotPoint(s.time, i + 1) for i, s in enumerate(successes)]

    def filter_projects(self, projects: list[str]) -> NamedEval:
        filtered_results: list[GeneralResult] = []
        for result in self.results:
            if result.file.parts[0] not in projects:
                continue
            filtered_results.append(result)
        return NamedEval(self.name, filtered_results)

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

    def filter_indexed_results(self, pairs: set[IndexedProofPair]) -> NamedEval:
        filtered: list[GeneralResult] = []
        seen_pairs: set[IndexedProofPair] = set()
        for result in self.results:
            assert result.file_idx is not None
            key = IndexedProofPair(result.file, result.theorem, result.file_idx)
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


@dataclass
class IndexedProofPair:
    file: Path
    theorem: str
    index: int

    def __hash__(self) -> int:
        return hash((self.file, self.theorem, self.index))


def get_mutual_indexed_proof_pairs(evals: list[NamedEval]) -> set[IndexedProofPair]:
    assert 0 < len(evals)
    mutual_pairs = evals[0].get_indexed_proof_pairs()
    for eval in evals[1:]:
        mutual_pairs &= eval.get_indexed_proof_pairs()
    return mutual_pairs


def get_mutual_proof_pairs(evals: list[NamedEval]) -> set[ProofPair]:
    assert 0 < len(evals)
    mutual_pairs = evals[0].get_non_duplicate_proof_pairs()
    for eval in evals[1:]:
        mutual_pairs &= eval.get_non_duplicate_proof_pairs()
    return mutual_pairs


# def get_mutual_proof_descs(evals: list[NamedEval]) -> set[ProofDesc]:
#     assert 0 < len(evals)
#     mutual_descs = evals[0].get_non_duplicate_proof_descs()
#     for eval in evals[1:]:
#         mutual_descs &= eval.get_non_duplicate_proof_descs()
#     return mutual_descs


# def get_mutually_successful_proof_pairs(
#     evals: list[NamedEval],
# ) -> dict[str, list[SuccessfulResult]]:
#     assert 0 < len(evals)
#     eval_successes = [e.get_successful_proof_pairs() for e in evals]
#     all_successes = set(eval_successes[0].keys())
#     for e in evals[1:]:
#         e_successes = set(e.get_successful_proof_pairs().keys())
#         all_successes &= e_successes

#     success_dict: dict[str, list[SuccessfulResult]] = dict(
#         [(e.name, []) for e in evals]
#     )
#     for easy_proof in all_successes:
#         for e, e_succeses in zip(evals, eval_successes):
#             success_dict[e.name].append(e_succeses[easy_proof])
#     for k, v in success_dict.items():
#         assert len(v) == len(all_successes)
#     return success_dict


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
    modules: list[str]
    file_idx: Optional[int]
    proof: Optional[str]
    num_deps: Optional[int]
    num_proj_deps: Optional[int]
    num_proofs_available: Optional[int]

    def __lt__(self, other: GeneralResult) -> bool:
        return (self.file, self.theorem) < (other.file, other.theorem)

    GIT_NAMES = ["coq-community", "coq-contribs", "thery", "AbsInt", "CertiKOS"]

    # def get_desc(self) -> ProofDesc:
    #     return ProofDesc(self.file, self.theorem, ".".join(self.modules))

    def to_json(self) -> Any:
        return {
            "file": str(self.file),
            "raw_file": str(self.raw_file),
            "theorem": self.theorem,
            "time": self.time,
            "modules": self.modules,
            "success": self.success,
            "file_idx": self.file_idx,
            "proof": self.proof,
            "num_deps": self.num_deps,
            "num_proj_deps": self.num_proj_deps,
            "num_proofs_available": self.num_proofs_available,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> GeneralResult:
        return cls(
            Path(json_data["file"]),
            Path(json_data["raw_file"]),
            json_data["theorem"],
            json_data["time"],
            json_data["success"],
            json_data["modules"],
            json_data.get("file_idx", None),
            json_data["proof"],
            json_data["num_deps"],
            json_data["num_proj_deps"],
            json_data["num_proofs_available"],
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
            cls.normalize_thm(kill_comments(result.thm_str)),
            result.time,
            result.success,
            result.module,
            None,
            result.proof,
            None,
            None,
            None,
        )

    @classmethod
    def clean_proverbot_path(cls, file_path: Path) -> Path:
        return cls.strip_path(Path(file_path.parts[0]) / file_path.name)

    @classmethod
    def strip_path(cls, path: Path) -> Path:
        for name in cls.GIT_NAMES:
            dashed_name = f"{name}-"
            if str(path).startswith(dashed_name):
                return Path(str(path)[len(dashed_name) :])
        return path

    @classmethod
    def clean_tactician_path(cls, file_path: Path) -> Path:
        assert file_path.parts[0] == "repos"
        rel_path = file_path.relative_to("repos")
        stripped_path = cls.strip_path(rel_path)
        return Path(stripped_path.parts[0]) / stripped_path.name

    @classmethod
    def clean_rango_path(cls, file_path: Path) -> Path:
        if file_path.is_relative_to("raw-data/coq-dataset/repos"):
            rel_path = file_path.relative_to("raw-data/coq-dataset/repos")
        elif file_path.is_relative_to("raw-data/cutoff-eval-dataset/repos"):
            rel_path = file_path.relative_to("raw-data/cutoff-eval-dataset/repos")
        else:
            raise ValueError(f"Unexpected path {file_path}")
        stripped_path = cls.strip_path(rel_path)
        return Path(stripped_path.parts[0]) / stripped_path.name

    @classmethod
    def from_tactician_result(cls, result: TacticianResult) -> GeneralResult:
        return cls(
            cls.clean_tactician_path(Path(result.file_name)),
            Path(result.file_name),
            cls.normalize_thm(result.thm_str),
            result.time,
            result.success,
            result.module if result.module is not None else [],
            result.file_idx,
            (
                cls.get_tactician_proof(result.proof)
                if result.success and result.proof is not None
                else None
            ),
            None,
            None,
            None,
        )

    @classmethod
    def from_rango_summary(cls, result: Summary) -> GeneralResult:
        assert isinstance(result, StraightLineSummary)
        proof = None
        file_idx = result.proof_idx
        if result.success:
            assert result.attempts is not None
            assert result.proof is not None
            assert result.attempts[-1] in result.proof
            proof = result.attempts[-1]
        if result.file.is_relative_to("raw-data/coq-dataset"):
            clean_file_path = result.file.relative_to("raw-data/coq-dataset")
        elif result.file.is_relative_to("raw-data/cutoff-eval-dataset"):
            clean_file_path = result.file.relative_to("raw-data/cutoff-eval-dataset")
        else:
            raise ValueError(f"Unexpected path {result.file}")

        return cls(
            cls.clean_rango_path(result.file),
            clean_file_path,
            cls.normalize_thm(result.theorem),
            result.search_time if result.search_time is not None else -1,
            result.success,
            result.module,
            file_idx,
            proof,
            None,
            None,
            None,
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
    return [GeneralResult.from_tactician_result(r) for r in tactician_results]


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
    module: Optional[list[str]]
    file_idx: int
    time: float
    timeout: bool
    proof: Optional[str]

    @classmethod
    def from_json(cls, json_data: Any, file_idx: int) -> TacticianResult:
        return cls(
            json_data["file"],
            json_data["theorem"],
            json_data["success"],
            json_data.get("module"),
            file_idx,
            json_data["synth_time"],
            json_data["timeout"],
            json_data["stdout"],
        )


def load_tactician_results(path: Path) -> list[TacticianResult]:
    results: list[TacticianResult] = []
    for result_file in os.listdir(path):
        with (path / result_file).open() as fin:
            result_data = json.load(fin)
            file_idx_match = re.search(r"(\d+)\.(json|v)$", result_file)
            assert file_idx_match is not None
            (file_idx_str, _) = file_idx_match.groups()
            result = TacticianResult.from_json(result_data, int(file_idx_str))
            results.append(result)
    return results


@dataclass
class ProverBotResult:
    project: str
    file_name: str
    thm_str: str
    module: list[str]
    success: bool
    time: float
    num_steps: int
    proof: Optional[str]

    META_IDX = 0
    META_PROJ_IDX = 0
    META_FILE_IDX = 1
    META_MODULE_IDX = 2
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
        module = metadata_json[cls.META_MODULE_IDX]
        assert 0 < len(module) and module.endswith(".")
        module_list_w_filename = module[:-1].split(".")
        assert 0 < len(module_list_w_filename)
        module_list = module_list_w_filename[1:]

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
        return cls(proj, file, thm, module_list, success, time, steps, proof)


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
