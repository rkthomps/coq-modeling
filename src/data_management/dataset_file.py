
from __future__ import annotations
from typing import Any

import sys, os
import jsonlines
import json
import pdb
import re

STEPS_NAME = "steps.jsonl"
FILE_CONTEXT_NAME = "file_context.jsonl"

class Sentence:
    bad_sentence_endings: set[str] = set()
    def __init__(self, 
                 text: str,
                 file_path: str,
                 module: list[str],
                 sentence_type: str,
                 line: int):
        assert type(text) == str
        try:
            assert text.strip().endswith(".")
        except AssertionError:
            if text.strip() not in self.bad_sentence_endings:
                self.bad_sentence_endings.add(text.strip())
                print(f"{file_path}:{line} Not Sentence: {text.strip()}")
        assert type(file_path) == str
        assert all([type(m) == str for m in module])
        assert type(sentence_type) == str
        assert type(line) == int
        self.text = text
        self.file_path = file_path
        self.module = module
        self.sentence_type = sentence_type
        self.line = line

    def __hash__(self) -> int:
        tup_module = tuple(self.module)
        return hash((self.text, self.file_path, tup_module, self.sentence_type, self.line))

    @classmethod
    def from_json(cls, json_data: Any) -> Sentence:
        text = json_data["text"]
        file_path = json_data["file_path"]
        module = json_data["module"]
        sentence_type = json_data["type"]
        line = json_data["line"]
        return cls(text, file_path, module, sentence_type, line)


class FileContext:
    def __init__(self, file: str, sentences: list[Sentence]) -> None:
        assert type(file) == str
        assert all([type(s) == Sentence for s in sentences])
        self.file = file
        self.sentences = sentences

    @classmethod
    def from_json(cls, json_data: Any) -> FileContext:
        file = json_data["file"]
        sentences: list[Sentence] = []
        for sentence_data in json_data["context"]:
            sentences.append(Sentence.from_json(sentence_data)) 
        return cls(file, sentences)


class Term:
    def __init__(self, 
                 term: Sentence,
                 term_context: list[Sentence]):
        assert type(term) == Sentence
        assert all([type(t) == Sentence for t in term_context])
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

    
    @classmethod
    def from_json(cls, json_data: Any) -> Term:
        term = Sentence.from_json(json_data)
        term_context: list[Sentence] = []
        for sentence in term_context:
            term_context.append(Sentence.from_json(sentence))
        return cls(term, term_context) 


class Step:
    bad_tactic_endings: set[str] = set()
    def __init__(self, text: str,
                 context: list[Sentence]) -> None:
        tactic_end_pattern = re.compile(r"([{}])|(\.)|([+\-*]+)$")
        try:
            assert tactic_end_pattern.search(text.strip()) != None
        except AssertionError:
            if text.strip() not in self.bad_tactic_endings:
                self.bad_tactic_endings.add(text.strip())
                print("Bad Tactic Ending", text)
        assert all([type(s) == Sentence for s in context]) 
        self.text = text
        self.context = context
    
    @classmethod
    def from_json(cls, json_data: Any) -> Step:
        text = json_data["text"]
        context: list[Sentence] = []
        for raw_sentence in json_data["context"]:
            context.append(Sentence.from_json(raw_sentence))
        return cls(text, context)


class Goal:
    def __init__(self, hyps: list[str], goal: str) -> None:
        assert type(hyps) == list
        assert all([type(h) == str for h in hyps])
        assert type(goal) == str
        self.hyps = hyps
        self.goal = goal

    def to_string(self) -> str:
        return "\n".join(self.hyps) + "\n\n" + self.goal

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


class FocusedStep:
    def __init__(self, term: Term,
                 step: Step,
                 n_step: int,
                 goals: list[Goal],
                 next_steps: list[Step]                 
                 ) -> None:
        assert type(term) == Term
        assert type(step) == Step
        assert type(n_step) == int
        assert all([type(g) == Goal for g in goals]) 
        assert all([type(s) == Step for s in next_steps])
        self.term = term
        self.step = step
        self.n_step = n_step
        self.goals = goals
        self.next_steps = next_steps

    def __hash__(self) -> int:
        # Can make more strict. This will do for now
        return hash((self.term, self.step.text, self.n_step))

    def __eq__(self, other: object) -> bool: 
        if not isinstance(other, FocusedStep):
            return False
        return hash(self) == hash(other)


    @classmethod
    def from_json(cls, json_data: Any) -> FocusedStep:
        term = Term.from_json(json_data["term"])
        step = Step.from_json(json_data["step"])
        n_step = json_data["n_step"]

        goals: list[Goal] = []
        for goal_data in json_data["goals"]:
            goals.append(Goal.from_json(goal_data))

        next_steps: list[Step] = []
        for next_step_data in json_data["next_steps"]:
            next_steps.append(Step.from_json(next_step_data))
        return FocusedStep(term, step, n_step, goals, next_steps) 


class Proof:
    def __init__(self, theorem: Term, steps: list[FocusedStep]) -> None:
        assert type(theorem) == Term
        assert type(steps) == list
        assert all([type(fs) == FocusedStep for fs in steps])

        self.theorem = theorem
        self.steps = steps

    def proof_text_to_string(self) -> str:
        theorem_text = self.theorem.term.text
        step_strings = [s.step.text for s in self.steps]
        proof_text = "".join(step_strings)
        return f"{theorem_text}{proof_text}"

    def proof_prefix_to_string(self, stop_step: FocusedStep) -> str:
        """Print the tactics of the proof up to but not including the given step"""
        proof = self.theorem.term.text
        for step in self.steps:
            if (step == stop_step):
                break
            proof += step.step.text
        return proof


class DatasetFile:
    def __init__(self, file: str,
                 avail_premises: list[Sentence],
                 proofs: list[Proof]) -> None:
        # TODO: Turn into list of proofs. 
        assert type(file) == str
        assert all([type(p) == Sentence for p in avail_premises]) 
        assert all([type(p) == Proof for p in proofs])
        self.file = file
        self.avail_premises = avail_premises 
        self.proofs = proofs 

    def proofs_to_string(self) -> str:
        proof_strings = [p.proof_text_to_string() for p in self.proofs]
        return "\n\n".join(proof_strings)

    @classmethod
    def __get_file_data(cls, file_context_loc: str) -> tuple[str, list[Sentence]]:
        file_context_json_lines: list[Any] = []
        with jsonlines.open(file_context_loc, "r") as fin:
            for obj in fin:
                file_context_json_lines.append(obj)
        assert len(file_context_json_lines) == 1
        file_context_json_data = file_context_json_lines[0]

        file = file_context_json_data["file"]

        avail_premises: list[Sentence] = []
        for sentence_data in file_context_json_data["context"]:
            avail_premises.append(Sentence.from_json(sentence_data))

        return file, avail_premises 

    @classmethod
    def __get_proofs(cls, steps_loc: str) -> list[Proof]:
        steps: list[FocusedStep] = []
        with jsonlines.open(steps_loc, "r") as fin:
            for obj in fin:
                steps.append(FocusedStep.from_json(obj))

        if len(steps) == 0:
            return []

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
    def from_directory(cls, dir_path: str) -> DatasetFile:
        file_context_loc = os.path.join(dir_path, FILE_CONTEXT_NAME)
        steps_loc = os.path.join(dir_path, STEPS_NAME)
        assert os.path.exists(file_context_loc)
        assert os.path.exists(steps_loc)
        
        file, avail_premises = cls.__get_file_data(file_context_loc)
        proofs = cls.__get_proofs(steps_loc)

        return cls(file, avail_premises, proofs)


if __name__ == "__main__":
    TEST_PATH = "raw-data/data-points-partial"
    for dirname in os.listdir(TEST_PATH):
        absolute_dirname = os.path.join(TEST_PATH, dirname)
        obj = DatasetFile.from_directory(absolute_dirname)
        print(f"\n\n{dirname}")
        print(obj.proofs_to_string())


