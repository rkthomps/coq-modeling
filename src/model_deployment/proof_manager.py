from __future__ import annotations
from typing import Any, Optional
from types import TracebackType

import sys, os
from enum import Enum
import ipdb
import time

from typeguard import typechecked

from util.util import get_fresh_path
from util.coqpyt_utils import (
    replace_proof_with_admitted_stub,
    restore_proof_file,
    go_through_point,
)
from data_management import dataset_file
from data_management.sentence_db import SentenceDB
from data_management.dataset_file import (
    DatasetFile,
    Proof,
    FocusedStep,
    Step,
    FileContext,
)
from data_management.splits import Split, FileInfo

from tactic_gen.lm_example import LmExample, LmFormatter, ProofRetrievalFormatter
from model_deployment.goal_comparer import (
    ParsedObligations,
    ParsedObligation,
    ParsedHyp,
    extract_body_from_step,
)
from model_deployment.fast_client import FastLspClient
from model_deployment.mine_goals import get_goal_record, GoalRecord
from util.util import get_basic_logger
from util.coqpyt_utils import get_all_goals

from coqpyt.lsp.client import LspClient
from coqpyt.coq.lsp.client import (
    TextDocumentIdentifier,
    TextDocumentItem,
    CoqLspClient,
    Position,
)
from coqpyt.coq.changes import CoqAddStep, CoqDeleteStep
from coqpyt.coq.structs import ProofTerm, Term, TermType, Step as CStep
from coqpyt.coq.lsp.structs import Goal, GoalAnswer, RangedSpan
from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.exceptions import InvalidChangeException

from coqpyt.lsp.structs import (
    TextDocumentIdentifier,
    VersionedTextDocumentIdentifier,
    TextDocumentContentChangeEvent,
    TextDocumentItem,
    Position,
    Range,
)


_logger = get_basic_logger(__name__)


class TacticResult(Enum):
    COMPLETE = 1
    VALID = 2
    INVALID = 3


@typechecked
class ProofCheckResult:
    def __init__(
        self,
        tactic_result: TacticResult,
        attempted_steps: list[str],
        current_goals: Optional[GoalAnswer],
        parsed_current_goals: Optional[ParsedObligations],
        goal_record: Optional[GoalRecord],
        new_proof: Optional[Proof],
    ) -> None:
        self.tactic_result = tactic_result
        self.attempted_steps = attempted_steps
        self.current_goals = current_goals
        self.parsed_current_goals = parsed_current_goals
        self.goal_record = goal_record
        self.new_proof = new_proof

    @classmethod
    def get_invalid(cls) -> ProofCheckResult:
        current_goals = None
        parsed_current_goals = None
        goal_record = None
        new_dataset_file = None
        return cls(
            TacticResult.INVALID,
            [],
            current_goals,
            parsed_current_goals,
            goal_record,
            new_dataset_file,
        )


def proc_file_path(file_path: str) -> str:
    if file_path.startswith("/home"):
        return "/".join(file_path.split("/")[3:])
    return file_path


def get_context(context: list[Term]) -> list[dict[str, Any]]:
    res: list[dict[str, Any]] = []
    for term in context:
        res.append(
            {
                "text": term.text,
                "file_path": proc_file_path(term.file_path),
                "module": term.module,
                "type": str(term.type),
                "line": term.ast.range.start.line,
            }
        )
    return res


def get_prefix_from_str(file_str: str, search_token: str) -> Optional[str]:
    token_idx = file_str.find(search_token)
    if token_idx == -1:
        return None
    return file_str[:token_idx].strip()


def get_file_prefix(filename: str, search_token: str) -> Optional[str]:
    with open(filename, "r") as fin:
        file_contents = fin.read()
    return get_prefix_from_str(file_contents, search_token)


def get_last_proof_data_points(proof: ProofTerm) -> Any:
    data_points: list[dict[str, Any]] = []
    for i, step in enumerate(proof.steps):
        assert step.goals.goals is not None
        goals = list(map(lambda goal: repr(goal), step.goals.goals.goals))
        next_steps: list[dict[str, Any]] = []
        data_point = {
            "term": {
                "text": proof.text,
                "file_path": proc_file_path(proof.file_path),
                "module": proof.module,
                "type": str(proof.type),
                "line": proof.ast.range.start.line,
                "context": get_context(proof.context),
            },
            "step": {"text": step.text, "context": get_context(step.context)},
            "n_step": i + 1,
            "goals": goals,
            "next_steps": next_steps,
        }
        for next_step in proof.steps[i + 1 :]:
            next_steps.append(
                {"text": next_step.text, "context": get_context(next_step.context)}
            )
        data_points.append(data_point)
    return data_points


SEARCH_TOKEN = "<prove>"


def set_hidden_files(
    hidden_file_path: str, aux_hidden_file_path: str, prefix: str
) -> None:
    with open(hidden_file_path, "w") as fout:
        fout.write(f"{prefix}\nAdmitted.")
    with open(aux_hidden_file_path, "w") as fout:
        fout.write(f"{prefix}")


def initialize_hidden_files(orig_file_path: str) -> tuple[str, str]:
    """
    Find a fresh file path, and copy the contents of the original
    file to the fresh file up to the <prove> token. Replace the
    <prove> token with `Admitted`.
    """
    file_dirname = os.path.dirname(orig_file_path)
    file_basename = os.path.basename(orig_file_path)
    fresh_file_path = get_fresh_path(file_dirname, file_basename)
    fresh_aux_file_path = get_fresh_path(file_dirname, f"aux_{file_basename}")
    file_prefix = get_file_prefix(orig_file_path, SEARCH_TOKEN)
    if file_prefix is None:
        raise ValueError(f"Could not find search token {SEARCH_TOKEN}")
    set_hidden_files(fresh_file_path, fresh_aux_file_path, file_prefix)
    return fresh_file_path, fresh_aux_file_path


def hidden_files_from_prefix(orig_file_path: str, file_prefix: str) -> tuple[str, str]:
    file_dirname = os.path.dirname(orig_file_path)
    file_basename = os.path.basename(orig_file_path)
    fresh_file_path = get_fresh_path(file_dirname, file_basename)
    fresh_aux_file_path = get_fresh_path(file_dirname, f"aux_{file_basename}")
    prefix_no_tok = get_prefix_from_str(file_prefix, SEARCH_TOKEN)
    if prefix_no_tok is None:
        raise ValueError(f"Could not find search token {SEARCH_TOKEN}")
    set_hidden_files(fresh_file_path, fresh_aux_file_path, prefix_no_tok)
    return fresh_file_path, fresh_aux_file_path

class ClientWrapper:
    def __init__(self, client: CoqLspClient | FastLspClient, file_uri: str) -> None:
        self.client = client
        self.file_uri = file_uri
        self.file_version = 1
        self.client.didOpen(TextDocumentItem(self.file_uri, "coq", self.file_version, ""))
    
    def set_version(self, v: int) -> None:
        self.file_version = v
    
    def write(self, content: str) -> None:
        self.file_version += 1
        self.client.didChange(VersionedTextDocumentIdentifier(self.file_uri, self.file_version), [TextDocumentContentChangeEvent(None, None, content)])
    
    def write_and_get_steps(self, content: str) -> list[CStep]:
        t1 = time.time()
        self.write(content)
        lines = content.split("\n")
        spans = self.client.get_document(TextDocumentIdentifier(self.file_uri)).spans
        steps: list[CStep] = []
        prev_line, prev_char = (0, 0)
        for i, span in enumerate(spans):
            if i == len(spans) - 1 and span.span is None:
                continue
            end_line, end_char = (spans[i].range.end.line, spans[i].range.end.character)
            cur_lines = lines[prev_line:(end_line + 1)]
            cur_lines[0] = cur_lines[0][prev_char:]
            cur_lines[-1] = cur_lines[-1][:end_char]
            prev_line, prev_char = end_line, end_char
            text = "\n".join(cur_lines)
            steps.append(CStep(text, "", span))
        t2 = time.time()
        print("Change time: ", t2 - t1)
        return steps
    
    def close(self) -> None:
        self.client.shutdown()
        self.client.exit()



@typechecked
class ProofManager:
    TIMEOUT = 60

    def __init__(
        self,
        file_path: str,
        proof_file: ProofFile,
        proof_point: int,
        lm_formatter: LmFormatter,
        file_info: FileInfo,
        sentence_db: SentenceDB,
        split: Split,
        data_loc: str,
    ) -> None:
        file_dir = os.path.dirname(file_path)
        file_basename = os.path.basename(file_path)
        self.file_path = file_path
        self.lm_formatter = lm_formatter

        self.proof_file = proof_file
        self.proof_point = proof_point
        self.sentence_db = sentence_db

        self.file_info = file_info
        self.split = split
        self.data_loc = data_loc

        self.__workspace_loc = os.path.join(self.data_loc, self.file_info.workspace)
        self.file_prefix = self.__get_file_prefix()
        self.__proof_stored_steps = replace_proof_with_admitted_stub(
            self.proof_file, self.proof_point
        )

        self.workspace_uri= f"file://{self.__workspace_loc}"



        self.fast_aux_file_path = os.path.abspath(get_fresh_path(file_dir, f"aux_fast_{file_basename}"))
        fast_aux_client = FastLspClient(self.workspace_uri, timeout=120)
        fast_aux_file_uri = f"file://{self.fast_aux_file_path}"
        self.fast_client = ClientWrapper(fast_aux_client, fast_aux_file_uri)

        self.aux_file_path = os.path.abspath(get_fresh_path(file_dir, f"aux_{file_basename}"))
        aux_file_uri = f"file://{self.aux_file_path}"
        aux_client = CoqLspClient(self.workspace_uri, timeout=120)
        self.aux_client = ClientWrapper(aux_client, aux_file_uri)

        # self.goal_file_path = get_fresh_path(file_dir, "aux_goals.v")
        # self.goal_file_uri = f"file://{self.goal_file_path}"
        # self.goal_client_root_version = 1
        # self.aux_client.didOpen(
        #     TextDocumentItem(
        #         self.goal_file_uri, "coq", self.goal_file_version, self.file_prefix
        #     )
        # )



    def __get_file_prefix(self) -> str:
        return "".join(
            [s.text for s in self.proof_file.steps[: (self.proof_point + 1)]]
        )

    def __get_current_partial_proof(self) -> list[str]:
        start_idx = self.proof_point + 1
        stop_idx = self.proof_file.steps_taken
        return [s.text for s in self.proof_file.steps[start_idx:stop_idx]]

    def set_proof_file(
        self,
        steps: list[str],
    ) -> None:
        current_partial_proof = self.__get_current_partial_proof()
        prefix_len = 0
        while (
            prefix_len < len(current_partial_proof)
            and prefix_len < len(steps)
            and current_partial_proof[prefix_len] == steps[prefix_len]
        ):
            prefix_len += 1

        num_steps_to_delete = len(current_partial_proof) - prefix_len
        delete_steps = [
            CoqDeleteStep(self.proof_point + prefix_len + i)
            for i in range(num_steps_to_delete, 0, -1)
        ]
        add_steps = [
            CoqAddStep(s, self.proof_point + prefix_len + i)
            for i, s in enumerate(steps[prefix_len:])
        ]
        self.proof_file.change_steps(delete_steps + add_steps)
        go_through_point(self.proof_file, self.proof_point + len(steps))
        assert "Admitted." in self.proof_file.steps[self.proof_file.steps_taken].text

    def __update_aux_file(self, partial_proof: str) -> None:
        with open(self.aux_file_path, "w") as fout:
            fout.write(f"{self.file_prefix}{partial_proof}")

    def __get_goal_strs(self, current_goals: GoalAnswer) -> list[str]:
        all_goals = get_all_goals(current_goals)
        final_strings: list[str] = []
        for i, goal in enumerate(all_goals):
            for j, hyp in enumerate(goal.hyps):
                final_strings.append(f"Definition g_{i}_h_{j} := ({hyp.ty}).")
            final_strings.append(f"Definition g_{i} := ({goal.ty}).")
        return final_strings

    def __read_definition(
        self, steps: list[CStep], num_definitions: int, num_read: int
    ) -> tuple[Any, str, int]:
        num_steps = len(steps)
        read_idx = num_steps - num_definitions + num_read
        def_text = steps[read_idx].text
        ast_def_body = extract_body_from_step(steps[read_idx])
        return ast_def_body, def_text, num_read + 1

    def get_goal_record(self, steps: list[str]) -> Optional[GoalRecord]:
        if not isinstance(self.lm_formatter, ProofRetrievalFormatter):
            return None
        new_step_idx = self.proof_point + len(steps)
        end_pos = self.proof_file.steps[new_step_idx].ast.range.end
        goal_dict: dict[int, Optional[GoalAnswer]] = {}
        record, version = get_goal_record(
            self.fast_client.client,
            self.fast_client.file_uri,
            self.fast_client.file_version,
            end_pos,
            self.proof_file.steps,
            new_step_idx,
            goal_dict,
        )
        self.fast_client.set_version(version)
        return record

    def get_parsed_goals(
        self, partial_proof: str, current_goals: GoalAnswer
    ) -> ParsedObligations:
        assert current_goals.goals is not None
        all_goals = get_all_goals(current_goals)
        _logger.debug(f"Num goals: {len(all_goals)}")
        goal_as_definitions = self.__get_goal_strs(current_goals)
        goal_str = "\n\n".join(goal_as_definitions)
        to_write = f"{self.file_prefix}{partial_proof}\n\n{goal_str}"
        steps = self.fast_client.write_and_get_steps(to_write)

        ##self.__update_aux_file(to_write)
        num_read = 0
        num_definitions = len(goal_as_definitions)
        parsed_goals: list[ParsedObligation] = []
        for goal in all_goals:
            parsed_hyps: list[ParsedHyp] = []
            for hyp in goal.hyps:
                hyp_ast, hyp_text, num_read = self.__read_definition(
                    steps, num_definitions, num_read
                )
                parsed_hyp = ParsedHyp(hyp.names, hyp_ast, hyp_text)
                parsed_hyps.append(parsed_hyp)
            goal_ast, goal_text, num_read = self.__read_definition(
                steps, num_definitions, num_read
            )
            parsed_goal = ParsedObligation(parsed_hyps, goal_ast, goal_text)
            parsed_goals.append(parsed_goal)
        return ParsedObligations(parsed_goals)

    def get_proof_shell(
        self, cur_steps: list[str], cur_goals: GoalAnswer, theorem: dataset_file.Term
    ) -> Proof:
        focused_steps: list[FocusedStep] = []
        for i, step in enumerate(cur_steps):
            focused_steps.append(
                FocusedStep(theorem, Step.from_text(step, TermType.TACTIC), i, [])
            )

        goals = [dataset_file.Goal.from_json(repr(g)) for g in cur_goals.goals.goals]
        focused_steps.append(
            FocusedStep(
                theorem,
                Step.from_text("\nAdmitted.", TermType.TACTIC),
                len(cur_steps),
                goals,
            )
        )
        proof = Proof(theorem, focused_steps)
        return proof

    def __can_close_proof(self, goals: Optional[GoalAnswer]):
        def empty_stack(stack: list[tuple[list[Goal], list[Goal]]]):
            # e.g. [([], [])]
            for tuple in stack:
                if len(tuple[0]) > 0 or len(tuple[1]) > 0:
                    return False
            return True

        if goals is None:
            return False

        inner_goals = goals.goals
        if inner_goals is None:
            return False

        return (
            len(inner_goals.goals) == 0
            and empty_stack(inner_goals.stack)
            and len(inner_goals.shelf) == 0
            and inner_goals.bullet is None
        )

    def get_initial_context(self) -> Optional[DatasetFile]:
        try:
            self.set_proof_file([])
        except InvalidChangeException:
            return None
        dset_file = self.get_dataset_file()
        return dset_file
    
    def check_valid(self, client: CoqLspClient) -> bool:
        for diagnostic in client.lsp_endpoint.diagnostics[self.aux_client.file_uri]:
            if diagnostic.severity == 1:
                return False
        return True

    def check_proof(
        self, partial_proof: str, theorem: dataset_file.Term
    ) -> ProofCheckResult:
        # TODO: NEED TO CATCH SIMPL IN *
        # partial_steps = separate_steps(partial_proof)
        if (
            ("Admitted." in partial_proof)
            or ("admit." in partial_proof)
            or ("Abort." in partial_proof)
        ):
            return ProofCheckResult.get_invalid()
        t1 = time.time()
        contents = f"{self.file_prefix}{partial_proof}"
        #steps = self.aux_client.write_and_get_steps(contents)
        steps = self.fast_client.write_and_get_steps(contents)
        # if not self.check_valid(self.aux_client.client):
        #     return ProofCheckResult.get_invalid()
        partial_steps = [s.text for s in steps[(self.proof_point + 1) :]]
        end_pos = steps[-1].ast.range.end
        farther_end = Position(end_pos.line + 1, 0)
        #current_goals = self.aux_client.client.proof_goals(TextDocumentIdentifier(self.aux_client.file_uri), farther_end) 
        current_goals = self.fast_client.client.proof_goals(TextDocumentIdentifier(self.fast_client.file_uri), farther_end) 
        if current_goals is None:
            return ProofCheckResult.get_invalid() 
        t2 = time.time()
        print("New check time:", t2 - t1)

        # self.__update_aux_file(partial_proof)
        # with CoqFile(self.aux_file_path, workspace=self.__workspace_loc) as coq_file:
        #     if not coq_file.is_valid:
        #         return ProofCheckResult.get_invalid()
        #     partial_steps = [s.text for s in coq_file.steps[(self.proof_point + 1) :]]
        #     end_pos = coq_file.steps[-1].ast.range.end
        #     farther_end = Position(end_pos.line + 1, 0)
        #     uri = f"file://{self.aux_file_path}"
        #     current_goals = coq_file.coq_lsp_client.proof_goals(
        #         TextDocumentIdentifier(uri), farther_end
        #     )
        #     if current_goals is None:
        #         return ProofCheckResult.get_invalid()

        try:
            assert "".join(partial_steps) == partial_proof
        except AssertionError:
            act = "".join(partial_steps)
            exp = partial_proof
            _logger.warning(f"Partial proof mismatch: expected '{exp}' got '{act}'")
            # ipdb.set_trace()

        if len(partial_steps) > 0 and "Qed." in partial_steps[-1]:
            # We detect qed ourselves.
            partial_steps = partial_steps[:-1]

        if self.__can_close_proof(current_goals):
            parsed_obligations = None
            goal_record = None
            proof = None
            return ProofCheckResult(
                TacticResult.COMPLETE,
                partial_steps,
                current_goals,
                parsed_obligations,
                goal_record,
                proof,
            )

        new_proof = self.get_proof_shell(partial_steps, current_goals, theorem)
        t1_g = time.time()
        parsed_obligations = self.get_parsed_goals(partial_proof, current_goals)
        t2_g = time.time()
        print("Parse goal time: ", t2_g - t1_g)
        goal_record = self.get_goal_record(partial_steps)
        return ProofCheckResult(
            TacticResult.VALID,
            partial_steps,
            self.proof_file.current_goals,
            parsed_obligations,
            goal_record,
            new_proof,
        )

    def get_example(
        self, dset_file: DatasetFile, goal_record: Optional[GoalRecord]
    ) -> LmExample:
        proof = dset_file.proofs[-1]
        last_step_idx = len(proof.steps) - 1
        example = self.lm_formatter.example_from_step(
            last_step_idx,
            proof,
            dp_obj=dset_file,
            file_info=self.file_info,
            split=self.split,
            data_loc=self.data_loc,
            ground_truth_steps=self.__proof_stored_steps,
            key_record=goal_record,
            cutoff_idx=self.proof_point,
        )
        return example

    def get_dataset_file(
        self,
    ) -> DatasetFile:
        self.proof_file.exec(1)  # Step past admitted
        last_proof = self.proof_file.proofs[-1]
        last_proof_data = get_last_proof_data_points(last_proof)
        context_list = list(self.proof_file.context.terms.values())
        context_data = get_context(context_list)
        proofs = DatasetFile.proofs_from_jsonl(last_proof_data, self.sentence_db)
        file_context_data = {
            "file": proc_file_path(last_proof.file_path),
            "workspace": proc_file_path(last_proof.file_path),
            "repository": "junkrepo",
            "context": context_data,
        }
        file_context = FileContext.from_verbose_json(file_context_data, self.sentence_db)
        self.proof_file.exec(-1)  # Return to before admitted (Point to last step)
        return DatasetFile(file_context, proofs)

    def __enter__(self) -> ProofManager:
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc_value: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        _logger.debug("Restoring proof file.")
        if os.path.exists(self.aux_file_path):
            os.remove(self.aux_file_path)
        if os.path.exists(self.fast_aux_file_path):
            os.remove(self.fast_aux_file_path)
        self.fast_client.close()
        self.aux_client.close()
        restore_proof_file(self.proof_file, self.proof_point, self.__proof_stored_steps)
