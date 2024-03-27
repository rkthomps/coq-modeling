from __future__ import annotations
from typing import Any, Optional
from enum import Enum
import sys, os
import jsonlines
import json
import re
import ipdb
import argparse
import time
import functools
import multiprocessing as mp


from data_management.sentence_db import SentenceDB, DBSentence

from typeguard import typechecked
from coqpyt.coq.structs import TermType

# from util.util import get_basic_logger

# _logger = get_basic_logger(__name__)


STEPS_NAME = "steps.jsonl"
FILE_CONTEXT_NAME = "file_context.jsonl"


def data_shape_expected(raw_data_loc: str) -> bool:
    for project in os.listdir(raw_data_loc):
        project_loc = os.path.join(raw_data_loc, project)
        if not os.path.isdir(project_loc):
            print(f"{project_loc} is not a directory.", file=sys.stderr)
            exit(1)
        project_files = set(os.listdir(project_loc))
        if not ((STEPS_NAME in project_files) and (FILE_CONTEXT_NAME in project_files)):
            print(
                f"{project_loc} does not contain files {STEPS_NAME} and {FILE_CONTEXT_NAME}"
            )
            exit(1)
    return True


@typechecked
class Sentence:
    bad_sentence_endings: set[str] = set()

    def __init__(
        self,
        text: str,
        file_path: str,
        module: list[str],
        sentence_type: TermType,
        line: int,
        db_idx: Optional[int] = None,
    ):
        try:
            assert text.strip().endswith(".")
        except AssertionError:
            if text.strip() not in self.bad_sentence_endings:
                self.bad_sentence_endings.add(text.strip())
                print(f"{file_path}:{line} Not Sentence: {text.strip()}")
        self.text = text
        self.file_path = file_path
        self.module = module
        self.sentence_type = sentence_type
        self.line = line
        self.db_idx = db_idx

    def __hash__(self) -> int:
        tup_module = tuple(self.module)
        # return hash(
        #     (self.text, self.file_path, tup_module, self.sentence_type, self.line)
        # )
        # The filepaths cause problems because they are different depending on where the
        # data was collected
        return hash((self.text, tup_module, self.sentence_type, self.line))

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
    def from_db_sentence(cls, db_sentence: DBSentence) -> Sentence:
        return Sentence(
            db_sentence.text,
            db_sentence.file_path,
            json.loads(db_sentence.module),
            TermType[db_sentence.sentence_type.split(".")[1]],
            db_sentence.line,
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

    @classmethod
    def from_json(cls, json_data: Any, sentence_db: SentenceDB) -> Sentence:
        if json_data["type"] == "stored":
            db_sentence = sentence_db.retrieve(json_data["id"])
            sentence = cls.from_db_sentence(db_sentence)
            return Sentence(
                sentence.text,
                sentence.file_path,
                sentence.module,
                sentence.sentence_type,
                sentence.line,
                json_data["id"],
            )

        text = json_data["text"]
        file_path = json_data["file_path"]
        module = json_data["module"]
        sentence_type = TermType[json_data["type"].split(".")[1]]
        line = json_data["line"]
        return cls(text, file_path, module, sentence_type, line)

    @classmethod
    def from_text(cls, text: str, term_type: TermType) -> Sentence:
        file_path = ""
        module = []
        line = -1
        return cls(text, file_path, module, term_type, line)


@typechecked
class Term:
    def __init__(self, term: Sentence, term_context: list[Sentence]):
        self.term = term
        self.term_context = term_context

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


@typechecked
class Step:
    bad_tactic_endings: set[str] = set()

    def __init__(self, text: str, context: list[Sentence]) -> None:
        tactic_end_pattern = re.compile(r"([{}])|(\.)|([+\-*]+)$")
        try:
            assert tactic_end_pattern.search(text.strip()) != None
        except AssertionError:
            if text.strip() not in self.bad_tactic_endings:
                self.bad_tactic_endings.add(text.strip())
                print("Bad Tactic Ending", text)
        self.text = text
        self.context = context

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


@typechecked
class Goal:
    def __init__(self, hyps: list[str], goal: str) -> None:
        self.hyps = hyps
        self.goal = goal

    def to_string(self) -> str:
        return "\n".join(self.hyps) + "\n\n" + self.goal

    def to_json(self) -> str:
        return self.to_string()

    @classmethod
    def from_json(cls, json_data: str) -> Goal:
        assert type(json_data) == str
        hyp_goal = json_data.split("\n\n")
        assert len(hyp_goal) <= 2
        assert len(hyp_goal) > 0
        if len(hyp_goal) == 1:
            return cls([], hyp_goal[0])
        hyps = hyp_goal[0].split("\n")
        return cls(hyps, hyp_goal[1])


@typechecked
class FocusedStep:
    def __init__(
        self,
        term: Term,
        step: Step,
        n_step: int,
        goals: list[Goal],
    ) -> None:
        self.term = term
        self.step = step
        self.n_step = n_step
        self.goals = goals

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


@typechecked
class Proof:
    def __init__(self, theorem: Term, steps: list[FocusedStep]) -> None:
        self.theorem = theorem
        self.steps = steps

    def proof_text_to_string(self, include_theorem: bool = True) -> str:
        theorem_text = self.theorem.term.text
        step_strings = [s.step.text for s in self.steps]
        proof_text = "".join(step_strings)
        if include_theorem:
            return f"{theorem_text}{proof_text}"
        else:
            return proof_text

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
    def from_json(cls, json_data: Any, sentence_db: SentenceDB) -> Proof:
        theorem = Term.from_json(json_data["theorem"], sentence_db)
        steps = [FocusedStep.from_json(s, sentence_db) for s in json_data["steps"]]
        return cls(theorem, steps)


@typechecked
class FileContext:
    def __init__(
        self, file: str, workspace: str, repository: str, avail_premises: list[Sentence]
    ) -> None:
        self.file = file
        self.workspace = workspace
        self.repository = repository
        self.avail_premises = avail_premises

    @classmethod
    def empty_context_from_lines(cls, lines: list[str]) -> FileContext:
        metadata_line = lines[0]
        metadata = json.loads(metadata_line)
        return cls(metadata["file"], metadata["workspace"], metadata["repository"], [])

    @classmethod
    @functools.lru_cache(maxsize=6000)
    def context_from_line(cls, line: str, sentence_db: SentenceDB) -> Sentence:
        line_data = json.loads(line)
        return Sentence.from_json(line_data, sentence_db)

    @classmethod
    def context_from_lines(cls, lines: list[str], sentence_db: SentenceDB) -> FileContext:
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


@typechecked
class DatasetFile:
    def __init__(self, file_context: FileContext, proofs: list[Proof]) -> None:
        # TODO: Turn into list of proofs.
        self.file_context = file_context
        self.proofs = proofs
        self.out_of_file_avail_premises = self.__get_oof_avail_premises()
        self.in_file_avail_premises = self.__get_in_file_avail_premises()
        self.dependencies = self.__get_dp_dependencies()

    def proofs_to_string(self) -> str:
        proof_strings = [p.proof_text_to_string() for p in self.proofs]
        return "\n\n".join(proof_strings)

    def __get_dp_dependencies(self) -> list[str]:
        dependencies: list[str] = []  # formatted as dp with / replaced with -
        for premise in self.file_context.avail_premises:
            repo_match = re.match(r"repos/(.*?\.v)", premise.file_path)
            if repo_match:
                (dp_unnorm_name,) = repo_match.groups()
                dp_norm_name = dp_unnorm_name.replace("/", "-")
                dependencies.append(dp_norm_name)
        return dependencies

    @classmethod
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
        for premise in self.file_context.avail_premises:
            norm_prem_path = self.fix_path(premise.file_path)
            norm_file_path = self.fix_path(self.file_context.file)
            if not self.__share_subpath(norm_prem_path, norm_file_path):
                oof_premises.add(premise)
        return list(oof_premises)

    def __get_in_file_avail_premises(self) -> list[Sentence]:
        in_file_premises: set[Sentence] = set()
        for premise in self.file_context.avail_premises:
            norm_prem_path = self.fix_path(premise.file_path)
            norm_file_path = self.fix_path(self.file_context.file)
            if self.__share_subpath(norm_prem_path, norm_file_path):
                in_file_premises.add(premise)
        return list(in_file_premises)

    def get_in_file_premises_before(self, proof: Proof) -> list[Sentence]:
        return [
            p for p in self.in_file_avail_premises if p.line < proof.theorem.term.line
        ]

    def get_premises_before(self, proof: Proof) -> list[Sentence]:
        return self.out_of_file_avail_premises + self.get_in_file_premises_before(proof)

    def save(self, path: str, sentence_db: SentenceDB, insert_allowed: bool) -> None:
        path_dirname = os.path.dirname(path)
        if 0 < len(path_dirname):
            os.makedirs(path_dirname, exist_ok=True)

        with open(path, "w") as fout:
            fout.write(json.dumps(self.to_json(sentence_db, insert_allowed), indent=2))

    def to_json(self, sentence_db: SentenceDB, insert_allowed: bool) -> Any:
        return {
            "file_context": self.file_context.to_jsonlines(sentence_db, insert_allowed),
            "proofs": [p.to_json(sentence_db, insert_allowed) for p in self.proofs],
        }

    @classmethod
    def load(
        cls, path: str, sentence_db: SentenceDB, metadata_only: bool = False
    ) -> DatasetFile:
        with open(path, "r") as fin:
            json_data = json.load(fin)
        return cls.from_json(json_data, sentence_db, metadata_only)

    @classmethod
    def from_json(
        cls, json_data: Any, sentence_db: SentenceDB, metadata_only: bool = False
    ) -> DatasetFile:
        if metadata_only:
            file_context = FileContext.empty_context_from_lines(
                json_data["file_context"]
            )
        else:
            file_context = FileContext.context_from_lines(json_data["file_context"], sentence_db)

        proofs = [Proof.from_json(p, sentence_db) for p in json_data["proofs"]]
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
            proofs.append(Proof(cur_term, cur_proof_steps))

            assert step.term not in seen_terms
            seen_terms.add(step.term)
            cur_term = step.term
            cur_proof_steps = [step]
        proofs.append(Proof(cur_term, cur_proof_steps))
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


def process_dp(orig_dp_loc: str, new_dp_loc: str, sentence_db_loc: str) -> None:
    sentence_db = SentenceDB.load(sentence_db_loc)
    t1 = time.time()
    dp = DatasetFile.from_directory(orig_dp_loc, sentence_db)
    t2 = time.time()
    print("Load time: ", t2 - t1)
    dp.save(new_dp_loc, sentence_db, True)
    t3 = time.time()
    print("Save time: ", t3 - t2)
    sentence_db.close()


def process_dps(orig_dp_dir: str, new_dp_dir: str, sentence_db_loc: str) -> None:
    sentence_db = SentenceDB.load(sentence_db_loc)
    for dp_name in os.listdir(orig_dp_dir):
        old_loc = os.path.join(orig_dp_dir, dp_name)
        new_loc = os.path.join(new_dp_dir, dp_name)
        t1 = time.time()
        dp = DatasetFile.from_directory(old_loc, sentence_db)
        t2 = time.time()
        print("Load time: ", t2 - t1)
        dp.save(new_loc, sentence_db, True)
        t3 = time.time()
        print("Save time: ", t3 - t2)
    sentence_db.close()


def get_mp_args(
    orig_dp_dir: str, new_dp_dir: str, sentence_db_loc: str
) -> list[tuple[str, str, str]]:
    transform_args: list[tuple[str, str, str]] = []
    for dp_name in os.listdir(orig_dp_dir):
        old_loc = os.path.join(orig_dp_dir, dp_name)
        new_loc = os.path.join(new_dp_dir, dp_name)
        transform_args.append((old_loc, new_loc, sentence_db_loc))
    return transform_args


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        "Convert data-points into a more concise format for faster loading."
    )
    parser.add_argument(
        "orig_dp_dir", help="Directory containing original verbose data points files."
    )
    parser.add_argument(
        "new_dp_dir", help="Directory to save new concise data points files."
    )
    parser.add_argument("sentence_db_loc", help="Location of sentence database.")

    args = parser.parse_args(sys.argv[1:])
    # num_procs = 0
    # if args.num_procs is not None:
    #     num_procs = args.num_procs

    if not os.path.exists(args.sentence_db_loc):
        SentenceDB.create(args.sentence_db_loc)

    process_dps(args.orig_dp_dir, args.new_dp_dir, args.sentence_db_loc)

    # transformation_args = get_mp_args(args.orig_dp_dir, args.new_dp_dir, args.sentence_db_loc)
    # with mp.Pool(args.num_procs) as pool:
    #     pool.starmap(process_dp, transformation_args)
