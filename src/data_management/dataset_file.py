from __future__ import annotations
from typing import Any, Optional
from enum import Enum
import sys, os
import json
import re
import string
import functools
import multiprocessing as mp
from pathlib import Path
import hypothesis.strategies as st
from dataclasses import dataclass

import hypothesis.strategies

from data_management.sentence_db import SentenceDB, DBSentence

from coqpyt.coq.structs import TermType

from util.constants import DATA_POINTS_NAME

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


STEPS_NAME = "steps.jsonl"
FILE_CONTEXT_NAME = "file_context.jsonl"


ID_FORM = re.compile(r"[^\[\]\{\}\(\):=,\s]+")


def get_ids_from_goal(goal: Goal) -> tuple[list[str], list[str]]:
    goal_search_str = goal.goal
    hyp_search_str = ""
    h_ids: set[str] = set()
    for h in goal.hyps:
        h_ty = h.split(":")
        if len(h_ty) == 1:
            hyp_search_str += " " + h_ty[0]
        else:
            h_ids |= set(h_ty[0].split(", "))
            hyp_search_str += " " + "".join(h_ty[1:])
    hyp_found_ids = re.findall(ID_FORM, hyp_search_str)
    filtered_hyp_ids = [f for f in hyp_found_ids if f not in h_ids]
    goal_found_ids = re.findall(ID_FORM, goal_search_str)
    filtered_goal_ids = [f for f in goal_found_ids if f not in h_ids]
    return filtered_hyp_ids, filtered_goal_ids


def get_ids_from_sentence(s: Sentence) -> list[str]:
    sentence_ids = re.findall(ID_FORM, s.text)
    return sentence_ids


@dataclass
class Sentence:
    text: str
    file_path: str
    module: list[str]
    sentence_type: TermType
    line: int
    db_idx: Optional[int]

    def __hash__(self) -> int:
        tup_module = tuple(self.module)
        return hash(
            (self.text, self.file_path, tup_module, self.sentence_type, self.line)
        )

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Sentence):
            return False
        return hash(self) == hash(other)

    def to_db_sentence(self) -> DBSentence:
        return DBSentence(
            self.text,
            self.file_path,
            json.dumps(self.module),
            str(self.sentence_type),
            self.line,
        )

    @classmethod
    @functools.lru_cache(10000)
    def from_db_sentence(cls, db_sentence: DBSentence) -> Sentence:
        return Sentence(
            db_sentence.text,
            db_sentence.file_path,
            json.loads(db_sentence.module),
            TermType[db_sentence.sentence_type.split(".")[1]],
            db_sentence.line,
            None,
        )

    def to_json(self, sentence_db: SentenceDB, insert_allowed: bool) -> Any:
        db_sentence = self.to_db_sentence()
        if insert_allowed and self.db_idx is None:
            result_id = sentence_db.insert_sentence(db_sentence)
            return {
                "type": "stored",
                "id": result_id,
            }

        if self.db_idx is None:
            idx_option = sentence_db.find_sentence(db_sentence)
            if idx_option is None:
                return {
                    "type": "explicit",
                    "text": self.text,
                    "file_path": self.file_path,
                    "module": self.module,
                    "type": str(self.sentence_type),
                    "line": self.line,
                }
            else:
                return {
                    "type": "stored",
                    "id": idx_option,
                }

        return {
            "type": "stored",
            "id": self.db_idx,
        }

    @classmethod
    def from_idx(cls, idx: int, sentence_db: SentenceDB) -> Sentence:
        db_sentence = sentence_db.retrieve(idx)
        sentence = cls.from_db_sentence(db_sentence)
        return Sentence(
            sentence.text,
            sentence.file_path,
            sentence.module,
            sentence.sentence_type,
            sentence.line,
            idx,
        )

    @classmethod
    def from_json(cls, json_data: Any, sentence_db: SentenceDB) -> Sentence:
        if json_data["type"] == "stored":
            return cls.from_idx(json_data["id"], sentence_db)
        text = json_data["text"]
        file_path = json_data["file_path"]
        module = json_data["module"]
        sentence_type = TermType[json_data["type"].split(".")[1]]
        line = json_data["line"]
        return cls(text, file_path, module, sentence_type, line, None)

    @classmethod
    def from_text(cls, text: str, term_type: TermType) -> Sentence:
        file_path = ""
        module = []
        line = -1
        return cls(text, file_path, module, term_type, line, None)


st.register_type_strategy(
    Sentence,
    st.builds(
        Sentence,
        st.text(),
        st.text(),
        st.lists(st.text()),
        st.from_type(TermType),
        st.integers(min_value=0, max_value=2**16),
        st.none(),
    ),
)


@dataclass
class Term:
    term: Sentence
    term_context: list[Sentence]

    def __hash__(self) -> int:
        """
        Note, I don't hash the context because the term includes enough
        information to uniquely identify the theorem/lemma etc. Making this
        more strict wouldn't break anything.
        """
        return hash(self.term)

    def __eq__(self, other: object) -> bool:
        if type(other) != Term:
            return False
        return hash(self) == hash(other)

    def to_json(self, sentence_db: SentenceDB, insert_allowed: bool) -> Any:
        term_json = self.term.to_json(sentence_db, insert_allowed)
        context_json = {
            "context": [
                s.to_json(sentence_db, insert_allowed) for s in self.term_context
            ]
        }
        return term_json | context_json

    @classmethod
    def from_json(cls, json_data: Any, sentence_db: SentenceDB) -> Term:
        term = Sentence.from_json(json_data, sentence_db)
        term_context: list[Sentence] = []
        for sentence in json_data["context"]:
            term_context.append(Sentence.from_json(sentence, sentence_db))
        return cls(term, term_context)

    @classmethod
    def from_text(cls, text: str, term_type: TermType) -> Term:
        term = Sentence.from_text(text, term_type)
        context: list[Sentence] = []
        return cls(term, context)


@dataclass
class Step:
    text: str
    context: list[Sentence]

    def to_json(self, sentence_db: SentenceDB, insert_allowed: bool) -> Any:
        return {
            "text": self.text,
            "context": [s.to_json(sentence_db, insert_allowed) for s in self.context],
        }

    @classmethod
    def from_json(cls, json_data: Any, sentence_db: SentenceDB) -> Step:
        text = json_data["text"]
        context: list[Sentence] = []
        for raw_sentence in json_data["context"]:
            context.append(Sentence.from_json(raw_sentence, sentence_db))
        return cls(text, context)

    @classmethod
    def from_text(cls, text: str, term_type: TermType) -> Step:
        context: list[Sentence] = []
        return cls(text, context)


class Goal:
    def __init__(self, hyps: list[str], goal: str) -> None:
        self.hyps = hyps
        self.goal = goal
        self.cached_hyp_ids: Optional[list[str]] = None
        self.cached_goal_ids: Optional[list[str]] = None

    def get_ids(self) -> tuple[list[str], list[str]]:
        if self.cached_hyp_ids is None or self.cached_goal_ids is None:
            self.cached_hyp_ids, self.cached_goal_ids = get_ids_from_goal(self)
        return self.cached_hyp_ids, self.cached_goal_ids

    def to_string(self) -> str:
        return "\n".join(self.hyps) + "\n\n" + self.goal

    def to_json(self) -> str:
        return self.to_string()

    @classmethod
    def from_json(cls, json_data: str) -> Goal:
        assert type(json_data) == str
        hyp_goal = json_data.split("\n\n")
        try:
            assert len(hyp_goal) <= 2
        except AssertionError:
            print(hyp_goal)
        assert len(hyp_goal) > 0
        if len(hyp_goal) == 1:
            return cls([], hyp_goal[0])
        hyps = hyp_goal[0].split("\n")
        return cls(hyps, hyp_goal[1])


hypothesis.strategies.register_type_strategy(
    Goal,
    st.builds(
        Goal,
        st.lists(st.text(alphabet=string.ascii_letters), min_size=0),
        st.text(alphabet=string.ascii_letters),
    ),
)


@dataclass
class FocusedStep:
    term: Term
    step: Step
    n_step: int
    goals: list[Goal]

    def __hash__(self) -> int:
        # Can make more strict. This will do for now
        return hash((self.term, self.step.text, self.n_step))

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, FocusedStep):
            return False
        return hash(self) == hash(other)

    def to_json(self, sentence_db: SentenceDB, insert_allowed: bool) -> Any:
        return {
            "term": self.term.to_json(sentence_db, insert_allowed),
            "step": self.step.to_json(sentence_db, insert_allowed),
            "n_step": self.n_step,
            "goals": [g.to_json() for g in self.goals],
        }

    @classmethod
    def from_json(cls, json_data: Any, sentence_db: SentenceDB) -> FocusedStep:
        term = Term.from_json(json_data["term"], sentence_db)
        step = Step.from_json(json_data["step"], sentence_db)
        n_step = json_data["n_step"]

        goals: list[Goal] = []
        for goal_data in json_data["goals"]:
            goals.append(Goal.from_json(goal_data))

        return FocusedStep(term, step, n_step, goals)

    @classmethod
    def from_step_text(cls, step_text: str) -> FocusedStep:
        term = Term.from_text("", TermType.THEOREM)
        step = Step.from_text(step_text, TermType.TACTIC)
        n_step = 0
        goals: list[Goal] = []
        return cls(term, step, n_step, goals)

    @classmethod
    def from_step_and_goals(
        cls, theorem_stmt: str, step_text: str, goals: list[Goal]
    ) -> FocusedStep:
        term = Term.from_text(theorem_stmt, TermType.THEOREM)
        step = Step.from_text(step_text, TermType.TACTIC)
        n_step = 0
        goals = goals
        return cls(term, step, n_step, goals)


class Proof:
    name_matches = [
        re.compile(r"\S+\s+(\S+?)[\[\]\{\}\(\):=,\s]"),
    ]

    def __init__(self, theorem: Term, steps: list[FocusedStep], proof_idx: int) -> None:
        self.theorem = theorem
        self.steps = steps
        self.proof_idx = proof_idx
        self.__text_id: Optional[str] = None

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Proof):
            return False
        return (
            self.theorem == other.theorem
            and self.steps == other.steps
            and self.proof_idx == other.proof_idx
        )

    def is_proof_independent(self) -> bool:
        if 0 == len(self.steps):
            return True
        return "Defined" not in self.steps[-1].step.text

    def proof_text_id(self) -> str:
        if self.__text_id is not None:
            return self.__text_id
        proof_text = self.proof_text_to_string()
        self.__text_id = proof_text
        return self.__text_id

    def proof_text_to_string(self, include_theorem: bool = True) -> str:
        theorem_text = self.theorem.term.text
        step_strings = [s.step.text for s in self.steps]
        proof_text = "".join(step_strings)
        if include_theorem:
            return f"{theorem_text}{proof_text}"
        else:
            return proof_text

    def get_theorem_name(self) -> str:
        for name_pattern in self.name_matches:
            name_match = name_pattern.search(self.theorem.term.text)
            if name_match is not None:
                (name,) = name_match.groups()
                return name
        _logger.warning(f"Could not find name for theorem: {self.theorem.term.text}")
        return "Anon"

    def proof_prefix_to_string(
        self,
        stop_step: FocusedStep,
        include_proof: bool = False,
        include_theorem: bool = True,
    ) -> str:
        """Print the tactics of the proof up to but not including the given step"""
        if include_theorem:
            proof = self.theorem.term.text
        else:
            proof = ""
        if include_proof:
            proof += "\nProof."
        for step in self.steps:
            if step == stop_step:
                break
            proof += step.step.text
        return proof

    def to_json(self, sentence_db: SentenceDB, insert_allowed: bool) -> Any:
        return {
            "theorem": self.theorem.to_json(sentence_db, insert_allowed),
            "steps": [s.to_json(sentence_db, insert_allowed) for s in self.steps],
        }

    @classmethod
    def from_json(
        cls, json_data: Any, sentence_db: SentenceDB, proof_idx: int
    ) -> Proof:
        theorem = Term.from_json(json_data["theorem"], sentence_db)
        steps = [FocusedStep.from_json(s, sentence_db) for s in json_data["steps"]]
        return cls(theorem, steps, proof_idx)


st.register_type_strategy(
    Proof,
    st.builds(
        Proof,
        st.from_type(Term),
        st.lists(st.from_type(FocusedStep), min_size=0),
        st.integers(),
    ),
)


@dataclass
class FileContext:
    file: str
    workspace: str
    repository: str
    avail_premises: list[Sentence]

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, FileContext):
            return False
        return (
            self.file == other.file
            and self.workspace == other.workspace
            and self.repository == other.repository
            and self.avail_premises == other.avail_premises
        )

    @classmethod
    def empty_context_from_lines(cls, lines: list[str]) -> FileContext:
        metadata_line = lines[0]
        metadata = json.loads(metadata_line)
        return cls(metadata["file"], metadata["workspace"], metadata["repository"], [])

    @classmethod
    @functools.lru_cache(maxsize=50000)
    def context_from_line(cls, line: str, sentence_db: SentenceDB) -> Sentence:
        line_data = json.loads(line)
        return Sentence.from_json(line_data, sentence_db)

    @classmethod
    def context_from_lines(
        cls, lines: list[str], sentence_db: SentenceDB
    ) -> FileContext:
        empty_context = cls.empty_context_from_lines(lines)
        context_sentences: list[Sentence] = []
        for line in lines[1:]:
            context_sentence = cls.context_from_line(line, sentence_db)
            context_sentences.append(context_sentence)
        return cls(
            empty_context.file,
            empty_context.workspace,
            empty_context.repository,
            context_sentences,
        )

    def to_jsonlines(self, sentence_db: SentenceDB, insert_allowed: bool) -> list[str]:
        metadata_info = {
            "file": self.file,
            "workspace": self.workspace,
            "repository": self.repository,
        }
        context_info = [
            s.to_json(sentence_db, insert_allowed) for s in self.avail_premises
        ]

        metadata_line = json.dumps(metadata_info)
        context_lines = [json.dumps(l) for l in context_info]
        return [metadata_line] + context_lines

    @classmethod
    def from_verbose_json(cls, json_data: Any, sentence_db: SentenceDB) -> FileContext:
        file = json_data["file"]
        workspace = json_data["workspace"]
        repository = json_data["repository"]
        seen_sentences: set[Sentence] = set()
        avail_premises: list[Sentence] = []
        for sentence_data in json_data["context"]:
            sentence = Sentence.from_json(sentence_data, sentence_db)
            if sentence not in seen_sentences:
                avail_premises.append(sentence)
                seen_sentences.add(sentence)
        return cls(file, workspace, repository, avail_premises)

    @classmethod
    def from_directory(cls, dir_path: str, sentence_db: SentenceDB) -> FileContext:
        file_context_loc = os.path.join(dir_path, FILE_CONTEXT_NAME)
        file_context_data: Optional[Any] = None
        with open(file_context_loc, "r") as fin:
            for line in fin:
                match file_context_data:
                    case None:
                        file_context_data = json.loads(line)
                    case _:
                        raise ValueError(
                            f"File context data {file_context_loc} has more than one line."
                        )
        match file_context_data:
            case None:
                raise ValueError(f"File context data {file_context_loc} had no lines")
            case a:
                return cls.from_verbose_json(a, sentence_db)


@st.composite
def file_contexts_from_project(draw, project_prefix: str) -> FileContext:
    file_base = draw(st.text(alphabet=string.ascii_letters, min_size=1))
    file_path = Path(project_prefix) / f"{file_base}.v"
    return FileContext(
        str(file_path),
        project_prefix,
        project_prefix,
        draw(st.lists(st.from_type(Sentence), min_size=0)),
    )


@st.composite
def file_contexts(draw) -> FileContext:
    workspace = draw(st.text(alphabet=string.ascii_letters, min_size=1))
    file_path = (
        Path(workspace)
        / f"{draw(st.text(alphabet=string.ascii_letters, min_size=1))}.v"
    )
    return FileContext(
        str(file_path),
        workspace,
        workspace,
        draw(st.lists(st.from_type(Sentence), min_size=0)),
    )


st.register_type_strategy(FileContext, file_contexts())


@dataclass
class StepID:
    file: str
    proof_idx: int
    step_idx: int

    def __hash__(self) -> int:
        return hash((self.file, self.proof_idx, self.step_idx))

    def to_string(self) -> str:
        return json.dumps(self.to_json())

    def to_json(self) -> Any:
        return {
            "file": self.file,
            "proof_idx": self.proof_idx,
            "step_idx": self.step_idx,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> StepID:
        return cls(
            json_data["file"],
            json_data["proof_idx"],
            json_data["step_idx"],
        )

    @classmethod
    def from_string(cls, s: str) -> StepID:
        return cls.from_json(json.loads(s))

    @classmethod
    def from_step_idx(
        cls, step_idx: int, proof_idx: int, dset_file: DatasetFile
    ) -> StepID:
        return StepID(dset_file.dp_name, proof_idx, step_idx)


class DatasetFile:
    def __init__(self, file_context: FileContext, proofs: list[Proof]) -> None:
        # TODO: Turn into list of proofs.
        self.file_context = file_context
        self.proofs = proofs
        self.out_of_file_avail_premises = self.__get_oof_avail_premises()
        self.in_file_avail_premises = self.__get_in_file_avail_premises()
        self.dependencies = self.__get_dp_dependencies()
        self.__cached_dp_names: dict[str, str] = {}

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, DatasetFile):
            return False
        return self.file_context == other.file_context and self.proofs == other.proofs

    def proofs_to_string(self) -> str:
        proof_strings = [p.proof_text_to_string() for p in self.proofs]
        return "\n\n".join(proof_strings)

    @property
    def dp_name(self) -> str:
        if self.file_context.file in self.__cached_dp_names:
            return self.__cached_dp_names[self.file_context.file]
        dp_names = self.__get_dp_norm_and_unorm_name(self.file_context.file)
        if dp_names is None:
            raise ValueError(
                f"Expected data path {self.file_context.file} to have subpath starting with 'repos'"
            )
        norm_name, _ = dp_names
        self.__cached_dp_names[self.file_context.file] = norm_name
        return norm_name

    def __get_dp_norm_and_unorm_name(
        self, data_file_path: str
    ) -> Optional[tuple[str, str]]:
        repo_match = re.search(r"repos/(.*\.v)", data_file_path)
        if repo_match is None:
            return None
        (dp_unnorm_name,) = repo_match.groups()
        dp_norm_name = dp_unnorm_name.replace("/", "-")
        if (
            dp_norm_name == "DmxLarchey-Hydra-theories-Hydra.v"
        ):  # HACK; Not sure why hydra is named with upper case
            dp_norm_name = "DmxLarchey-Hydra-theories-hydra.v"
        return dp_norm_name, dp_unnorm_name

    def __get_dp_dependencies(self) -> list[str]:
        dependencies: list[str] = []  # formatted as dp with / replaced with -
        for premise in self.file_context.avail_premises:
            dp_names = self.__get_dp_norm_and_unorm_name(premise.file_path)
            if dp_names:
                dp_norm_name, dp_unnorm_name = dp_names
                if (
                    dp_unnorm_name in self.file_context.file
                    or self.file_context.file in dp_unnorm_name
                ):
                    continue
                if dp_norm_name not in dependencies:
                    dependencies.append(dp_norm_name)
        return dependencies

    @classmethod
    @functools.cache
    def fix_path(cls, path: str) -> str:
        while path.startswith("../") or path.startswith("..\\"):
            path = path[3:]
        return path

    @classmethod
    def __share_subpath(cls, path1: str, path2: str) -> bool:
        return path1.endswith(path2) or path2.endswith(path1)

    def __get_oof_avail_premises(self) -> list[Sentence]:
        """
        Not a direct comparison of paths.
        Consider zyla-random-proofs-Interpreter.v where premises
        can have file path ../coq-dataset/... and the file context
        can have file path /coq-dataset/....
        """
        oof_premises: set[Sentence] = set()
        norm_file_path = self.fix_path(self.file_context.file)
        for premise in self.file_context.avail_premises:
            norm_prem_path = self.fix_path(premise.file_path)
            if not self.__share_subpath(norm_prem_path, norm_file_path):
                oof_premises.add(premise)
        return list(oof_premises)

    def __get_in_file_avail_premises(self) -> list[Sentence]:
        in_file_premises: set[Sentence] = set()
        norm_file_path = self.fix_path(self.file_context.file)
        for premise in self.file_context.avail_premises:
            norm_prem_path = self.fix_path(premise.file_path)
            if self.__share_subpath(norm_prem_path, norm_file_path):
                in_file_premises.add(premise)
        return list(in_file_premises)

    def get_in_file_premises_before(self, proof: Proof) -> list[Sentence]:
        return [
            p for p in self.in_file_avail_premises if p.line < proof.theorem.term.line
        ]

    def get_premises_before(self, proof: Proof) -> list[Sentence]:
        return self.out_of_file_avail_premises + self.get_in_file_premises_before(proof)

    def save(self, path: Path, sentence_db: SentenceDB, insert_allowed: bool) -> None:
        os.makedirs(path.parent, exist_ok=True)
        with path.open("w") as fout:
            fout.write(json.dumps(self.to_json(sentence_db, insert_allowed), indent=2))

    def to_json(self, sentence_db: SentenceDB, insert_allowed: bool) -> Any:
        return {
            "file_context": self.file_context.to_jsonlines(sentence_db, insert_allowed),
            "proofs": [p.to_json(sentence_db, insert_allowed) for p in self.proofs],
        }

    def get_theorem(self, theorem_name: str) -> Proof:
        for proof in self.proofs:
            if proof.get_theorem_name() == theorem_name:
                return proof
        raise ValueError(f"Theorem {theorem_name} not found.")

    @classmethod
    def load(
        cls, path: Path, sentence_db: SentenceDB, metadata_only: bool = False
    ) -> DatasetFile:
        with path.open("r") as fin:
            json_data = json.load(fin)
        ret_obj = cls.from_json(json_data, sentence_db, metadata_only)
        return ret_obj

    @classmethod
    def from_json(
        cls, json_data: Any, sentence_db: SentenceDB, metadata_only: bool = False
    ) -> DatasetFile:
        if metadata_only:
            file_context = FileContext.empty_context_from_lines(
                json_data["file_context"]
            )
        else:
            file_context = FileContext.context_from_lines(
                json_data["file_context"], sentence_db
            )

        proofs = [
            Proof.from_json(p, sentence_db, i)
            for i, p in enumerate(json_data["proofs"])
        ]
        return cls(file_context, proofs)

    @staticmethod
    def proofs_from_steps(steps: list[FocusedStep]) -> list[Proof]:
        proofs: list[Proof] = []
        cur_proof_steps: list[FocusedStep] = []
        seen_terms: set[Term] = set()
        cur_term = steps[0].term
        seen_terms.add(cur_term)
        cur_proof_steps.append(steps[0])

        for step in steps[1:]:
            if step.term == cur_term:
                cur_proof_steps.append(step)
                continue
            proofs.append(Proof(cur_term, cur_proof_steps, len(proofs)))

            assert step.term not in seen_terms
            seen_terms.add(step.term)
            cur_term = step.term
            cur_proof_steps = [step]
        proofs.append(Proof(cur_term, cur_proof_steps, len(proofs)))
        return proofs

    @classmethod
    def proofs_from_jsonl(cls, jsonl_data: Any, sentence_db: SentenceDB) -> list[Proof]:
        steps = [FocusedStep.from_json(s, sentence_db) for s in jsonl_data]
        return cls.proofs_from_steps(steps)

    @classmethod
    def get_proofs(cls, dset_loc: str, sentence_db: SentenceDB) -> list[Proof]:
        steps_loc = os.path.join(dset_loc, STEPS_NAME)
        steps: list[FocusedStep] = []
        with open(steps_loc, "r") as fin:
            for line in fin:
                json_data = json.loads(line)
                steps.append(FocusedStep.from_json(json_data, sentence_db))

        if len(steps) == 0:
            return []

        return cls.proofs_from_steps(steps)

    @classmethod
    def from_directory(cls, dir_path: str, sentence_db: SentenceDB) -> DatasetFile:
        file_context = FileContext.from_directory(dir_path, sentence_db)
        proofs = cls.get_proofs(dir_path, sentence_db)
        return cls(file_context, proofs)


@st.composite
def dataset_file_from_project(draw, project_prefix: str) -> DatasetFile:
    file_context = draw(file_contexts_from_project(project_prefix))
    return DatasetFile(file_context, draw(st.lists(st.from_type(Proof), min_size=0)))


st.register_type_strategy(
    DatasetFile,
    st.builds(
        DatasetFile,
        st.from_type(FileContext),
        st.lists(st.from_type(Proof), min_size=0),
    ),
)


class DPCache:
    def __init__(self, cache_size: int = 128):
        self.__cached_dps: dict[str, DatasetFile] = {}
        self.__cached_keys: list[str] = []
        self.__cache_size = cache_size

    def get_dp(
        self, dp_name: str, data_loc: Path, sentence_db: SentenceDB
    ) -> DatasetFile:
        assert len(self.__cached_keys) == len(self.__cached_dps)
        if dp_name in self.__cached_dps:
            cur_idx = self.__cached_keys.index(dp_name)
            self.__cached_keys.pop(cur_idx)
            self.__cached_keys.insert(0, dp_name)
            return self.__cached_dps[dp_name]
        dp_loc = data_loc / DATA_POINTS_NAME / dp_name
        dp_obj = DatasetFile.load(dp_loc, sentence_db)
        self.__cached_dps[dp_name] = dp_obj
        self.__cached_keys.insert(0, dp_name)
        if self.__cache_size < len(self.__cached_keys):
            del self.__cached_dps[self.__cached_keys.pop()]
        return dp_obj
