from __future__ import annotations
from typing import Any, Optional
import os
import time
from enum import Enum
import tiktoken

import requests
import random
from pathlib import Path
from dataclasses import dataclass
from requests.adapters import Retry, HTTPAdapter

from data_management.dataset_file import Proof, DatasetFile

import openai
from openai.types.chat import (
    ChatCompletionUserMessageParam,
    ChatCompletionAssistantMessageParam,
)

openai.api_key = os.environ["OPENAI_API_KEY"]
from openai import OpenAI

from tactic_gen.lm_example import (
    LmExample,
    FormatterConf,
    formatter_conf_from_yaml,
)
from tactic_gen.lm_example import (
    LmFormatter,
    FormatterConf,
    formatter_conf_from_yaml,
    formatter_from_conf,
    formatter_update_ips,
)
from model_deployment.model_result import ModelResult

from proof_retrieval.proof_retriever import (
    ProofRetriever,
    ProofRetrieverConf,
    proof_retriever_conf_from_yaml,
    proof_retriever_from_conf,
    proof_conf_update_ips,
)

from util.util import get_basic_logger, FlexibleUrl

_logger = get_basic_logger(__name__)


@dataclass
class FidTacticGenConf:
    ALIAS = "fid"
    checkpoint_loc: Path
    formatter_confs: Optional[list[FormatterConf]]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> FidTacticGenConf:
        formatter_confs = None
        if "formatters" in yaml_data:
            formatter_confs = [
                formatter_conf_from_yaml(f) for f in yaml_data["formatters"]
            ]
        return cls(
            Path(yaml_data["checkpoint_loc"]),
            formatter_confs,
        )


@dataclass
class DecoderTacticGenConf:
    ALIAS = "decoder"
    checkpoint_loc: Path
    formatter_confs: Optional[list[FormatterConf]]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> DecoderTacticGenConf:
        formatter_confs = None
        if "formatters" in yaml_data:
            formatter_confs = [
                formatter_conf_from_yaml(f) for f in yaml_data["formatters"]
            ]
        return cls(
            Path(yaml_data["checkpoint_loc"]),
            formatter_confs,
        )


@dataclass
class LocalTacticGenClientConf:
    ALIAS = "client"
    urls: list[FlexibleUrl]
    formatter_confs: list[FormatterConf]

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        for url in self.urls:
            new_ip, new_port = port_map[url.id]
            url.ip = new_ip
            url.port = new_port
        [formatter_update_ips(f, port_map) for f in self.formatter_confs]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> LocalTacticGenClientConf:
        return cls(
            [FlexibleUrl.from_yaml(u) for u in yaml_data["urls"]],
            [formatter_conf_from_yaml(f) for f in yaml_data["formatters"]],
        )


class ScoreType(Enum):
    DEPTH = 0
    BREADTH = 1

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ScoreType:
        match yaml_data:
            case "depth":
                return cls.DEPTH
            case "breadth":
                return cls.BREADTH
            case _:
                raise ValueError(f"Invalid score type", {yaml_data})


@dataclass
class ModelFreeTacticGenClientConf:
    ALIAS = "model_free"
    retriever_conf: ProofRetrieverConf
    score_type: ScoreType

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        proof_conf_update_ips(self.retriever_conf, port_map)

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> ModelFreeTacticGenClientConf:
        return cls(
            proof_retriever_conf_from_yaml(yaml_data["retriever"]),
            ScoreType.from_yaml(yaml_data["score_type"]),
        )


class ModelFreeTacticGenClient:
    def __init__(self, retriever: ProofRetriever, score_type: ScoreType):
        self.retriever = retriever
        self.score_type = score_type

    def set_seed(self, seed: int) -> None:
        return

    def get_recs(
        self, step_idx: int, proof: Proof, dset_file: DatasetFile, n: int, **kwargs: Any
    ) -> ModelResult:
        similar_proof_steps = self.retriever.get_similar_proof_steps(
            step_idx, proof, dset_file, training=False
        )
        similar_tactics: list[str] = []
        scores: list[float] = []
        lengths: list[int] = []

        for proof, step_id in similar_proof_steps:
            similar_tactics.append(proof.steps[step_id.step_idx].step.text)
            match self.score_type:
                case ScoreType.DEPTH:
                    scores.append(1)
                case ScoreType.BREADTH:
                    scores.append(-1)
            lengths.append(1)
            if n <= len(similar_tactics):
                break
            assert len(similar_tactics) == len(scores) == len(lengths)
        return ModelResult(similar_tactics, scores, lengths)

    @classmethod
    def from_conf(cls, conf: ModelFreeTacticGenClientConf) -> ModelFreeTacticGenClient:
        return cls(proof_retriever_from_conf(conf.retriever_conf), conf.score_type)


@dataclass
class PrevProofTacticGenClientConf:
    ALIAS = "prev_proof"
    retriever_conf: ProofRetrieverConf

    def update_ips(self, port_map: dict[int, tuple[str, int]]):
        proof_conf_update_ips(self.retriever_conf, port_map)

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> PrevProofTacticGenClientConf:
        return cls(proof_retriever_conf_from_yaml(yaml_data["retriever"]))


class PrevProofTacticGenClient:
    def __init__(self, retriever: ProofRetriever):
        self.retriever = retriever

    def get_recs(
        self, step_idx: int, proof: Proof, dset_file: DatasetFile, n: int, **kwargs: Any
    ) -> ModelResult:
        similar_proof_steps = self.retriever.get_similar_proof_steps(
            step_idx, proof, dset_file, training=False
        )
        similar_proofs: set[str] = set()
        for proof, _ in similar_proof_steps:
            similar_proofs.add(proof.proof_text_to_string(include_theorem=False))
            if n <= len(similar_proofs):
                break
        return ModelResult(
            list(similar_proofs), [1] * len(similar_proofs), [1] * len(similar_proofs)
        )

    def set_seed(self, seed: int) -> None:
        return

    @classmethod
    def from_conf(cls, conf: PrevProofTacticGenClientConf) -> PrevProofTacticGenClient:
        return cls(proof_retriever_from_conf(conf.retriever_conf))


def find_truncate_idx(
    tokenizer: tiktoken.Encoding,
    lines: list[str],
    cur_ceiling: int,
    cur_floor: int,
    max_tokens: int,
) -> int:
    ## cur_ceiling is the lowest index s.t. the number of tokens is too many.
    ## cur_floor is the the largets index s.t. the number of tokens are allowed.
    if cur_floor - cur_ceiling <= 1:
        return cur_floor
    inc_num = (cur_floor - cur_ceiling) // 2
    next_idx = cur_ceiling + inc_num
    next_n_tokens = len(tokenizer.encode("\n".join(lines[next_idx:])))
    if max_tokens < next_n_tokens:
        ## Lower the ceiling
        return find_truncate_idx(tokenizer, lines, next_idx, cur_floor, max_tokens)
    else:
        return find_truncate_idx(tokenizer, lines, cur_ceiling, next_idx, max_tokens)


def truncate_lines(tokenizer: tiktoken.Encoding, s: str, max_tokens: int) -> str:
    assert 1 <= max_tokens
    encoding = tokenizer.encode(s)
    if len(encoding) <= max_tokens:
        return s
    lines = s.split("\n")
    assert 0 < len(lines)
    single_line_length = len(tokenizer.encode(lines[-1]))
    if max_tokens < single_line_length:
        return ""
    truncate_idx = find_truncate_idx(tokenizer, lines, 0, len(lines) - 1, max_tokens)
    return "\n".join(lines[truncate_idx:])


@dataclass
class OpenAIClientConf:
    model: str
    max_input_tokens: int
    ALIAS = "openai"

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> OpenAIClientConf:
        max_input_tokens = yaml_data.get("max_input_tokens", 4096)
        return cls(yaml_data["model"], max_input_tokens)


@dataclass
class OpenAIClient:
    model: str
    tokenizer: tiktoken.Encoding
    client: openai.OpenAI
    max_input_tokens: int

    example_prefix = "Inductive Fruit :=\n" "  | Apple\n" "  | Banana."

    example_theorem = "Theorem fruit_thm : forall (a : Fruit), a = Apple \/ a = Banana."

    example_proof_str = (
        "```coq\n"
        "Proof.\n"
        "  intros.\n"
        "  destruct a.\n"
        "  - left. reflexivity.\n"
        "  - right. reflexivity.\n"
        "Qed.\n"
        "```"
    )

    def extract_proof(self, proof_str: str) -> Optional[str]:
        start_str = "```coq"
        end_str = "```"
        if proof_str.startswith(start_str) and proof_str.endswith(end_str):
            return proof_str[len(start_str) : -len(end_str)]
        return None

    def get_str_user_prompt(self, prefix: str, theorem: str) -> str:
        instructions = (
            "Prove the given theorem in Coq. "
            "You are given the lines preceding the theorem in the Coq "
            "file after the tag [PREFIX]. "
            "You are given the theorem you are meant to prove after the tag [THEOREM]. "
            "You complete the proof of the theorem. You give the proof after the [PROOF] tag. "
        )
        return (
            f"{instructions}\n\n[PREFIX]\n{prefix}\n\n[THEOREM]\n{theorem}\n\n[PROOF]"
        )

    def set_seed(self, seed: int):
        return

    def get_user_prompt(self, prefix: str, proof: Proof) -> str:
        return self.get_str_user_prompt(prefix, proof.theorem.term.text)

    def num_tokens(self, s: str) -> int:
        return len(self.tokenizer.encode(s))

    def get_cost(self, input_tokens: int, output_tokens: int) -> float:
        match self.model:
            case "gpt-4o":
                return 5e-6 * input_tokens + 15e-6 * output_tokens
            case "gpt-4o-mini":
                return 0.15e-6 * input_tokens + 0.6e-6 * output_tokens
            case "o1-mini":
                return 3e-6 * input_tokens + 12e-6 * output_tokens
            case "o1-preview":
                return 15e-6 * input_tokens + 60e-6 * output_tokens
            case _:
                raise ValueError(f"Invalid model: {self.model}")

    def get_recs(
        self,
        step_idx: int,
        proof: Proof,
        dset_file: DatasetFile,
        n: int,
        file_prefix: str,
        **kwargs: Any,
    ) -> ModelResult:
        example_user_prompt = self.get_str_user_prompt(
            self.example_prefix, self.example_theorem
        )
        # example_tokens = self.num_tokens(example_user_prompt) + self.num_tokens(self.example_proof_str)
        # theorem_tokens = self.num_tokens(proof.theorem.term.text)

        self.get_cost(0, 0)
        current_user_prompt = self.get_user_prompt(file_prefix, proof)
        prompt = [
            {
                "role": "user",
                "content": example_user_prompt,
            },
            {
                "role": "assistant",
                "content": self.example_proof_str,
            },
            {
                "role": "user",
                "content": current_user_prompt,
            },
        ]
        print("GPT Request:")
        print(prompt)

        completion = self.client.chat.completions.create(
            messages=prompt,
            model=self.model,
        )
        attempt = completion.choices[0].message.content
        prompt_tokens = completion.usage.prompt_tokens
        completion_tokens = completion.usage.completion_tokens
        cost = self.get_cost(prompt_tokens, completion_tokens)

        assert attempt is not None
        print("GPT Response:")
        clean_attempt = self.extract_proof(attempt)
        if clean_attempt:
            final_result = clean_attempt
        else:
            final_result = attempt
        return ModelResult([final_result], [1], [1], [cost])

    @classmethod
    def from_conf(cls, conf: OpenAIClientConf) -> OpenAIClient:
        client = OpenAI(
            api_key=os.environ["OPENAI_API_KEY"],
            organization=os.environ["OPENAI_ORG_KEY"],
        )
        if conf.model == "o1-preview":
            tokenizer = tiktoken.encoding_for_model("gpt-4o")
        elif conf.model == "o1-mini":
            tokenizer = tiktoken.encoding_for_model("gpt-4o-mini")
        else:
            tokenizer = tiktoken.encoding_for_model(conf.model)
        return cls(conf.model, tokenizer, client, conf.max_input_tokens)


class LocalTacticGenClient:
    def __init__(self, urls: list[str], formatters: list[LmFormatter]) -> None:
        self.formatters = formatters

        self.session = requests.Session()
        # retries = Retry(total=5,
        #                 backoff_factor=0.1,
        #                 status_forcelist=[ 500, 502, 503, 504 ])
        # self.session.mount("http://", HTTPAdapter(max_retries=retries))
        self.urls = urls

    def get_recs(
        self,
        step_idx: int,
        proof: Proof,
        dset_file: DatasetFile,
        n: int,
        beam: bool = False,
        token_mask: Optional[str] = None,
        **kwargs: Any,
    ) -> ModelResult:
        assert 0 < len(self.formatters)
        example = self.formatters[0].example_from_step(
            step_idx, proof.proof_idx, dset_file
        )
        request_id = hash(example)
        request_data = {
            "method": "get_recs",
            "params": [
                example.to_json(),
                n,
                proof.proof_text_to_string(include_theorem=False),
                beam,
                token_mask,
            ],
            "jsonrpc": "2.0",
            "id": request_id,
        }

        chosen_url = random.choice(self.urls)

        start = time.time()
        response = self.session.post(chosen_url, json=request_data).json()
        end = time.time()
        if request_id != request_id:
            _logger.error("ID MISMATCH IN REQUESTS")
        assert response["id"] == request_id
        return ModelResult.from_json(response["result"])

    def set_seed(self, seed: int) -> None:
        request_data = {
            "method": "set_model_seed",
            "params": [seed],
            "jsonrpc": "2.0",
            "id": hash(seed),
        }
        chosen_url = random.choice(self.urls)
        self.session.post(chosen_url, json=request_data)

    @classmethod
    def from_conf(cls, conf: LocalTacticGenClientConf) -> TacticGenClient:
        return cls(
            [u.get_url() for u in conf.urls],
            [formatter_from_conf(f) for f in conf.formatter_confs],
        )


TacticGenClient = (
    LocalTacticGenClient
    | ModelFreeTacticGenClient
    | PrevProofTacticGenClient
    | OpenAIClient
)


def tactic_gen_client_from_conf(conf: TacticGenConf) -> TacticGenClient:
    match conf:
        case LocalTacticGenClientConf():
            return LocalTacticGenClient.from_conf(conf)
        case ModelFreeTacticGenClientConf():
            return ModelFreeTacticGenClient.from_conf(conf)
        case PrevProofTacticGenClientConf():
            return PrevProofTacticGenClient.from_conf(conf)
        case OpenAIClientConf():
            return OpenAIClient.from_conf(conf)
        case _:
            raise ValueError(f"Invalid tactic client config: {str(conf.__class__)}")


def tactic_conf_update_ips(conf: TacticGenConf, port_map: dict[int, tuple[str, int]]):
    match conf:
        case (
            LocalTacticGenClientConf()
            | ModelFreeTacticGenClientConf()
            | PrevProofTacticGenClientConf()
        ):
            conf.update_ips(port_map)
        case _:
            pass


TacticGenConf = (
    LocalTacticGenClientConf
    | ModelFreeTacticGenClientConf
    | PrevProofTacticGenClientConf
    | FidTacticGenConf
    | DecoderTacticGenConf
    | OpenAIClientConf
)


def tactic_gen_conf_from_yaml(yaml_data: Any) -> TacticGenConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case LocalTacticGenClientConf.ALIAS:
            return LocalTacticGenClientConf.from_yaml(yaml_data)
        case ModelFreeTacticGenClientConf.ALIAS:
            return ModelFreeTacticGenClientConf.from_yaml(yaml_data)
        case PrevProofTacticGenClientConf.ALIAS:
            return PrevProofTacticGenClientConf.from_yaml(yaml_data)
        case DecoderTacticGenConf.ALIAS:
            return DecoderTacticGenConf.from_yaml(yaml_data)
        case FidTacticGenConf.ALIAS:
            return FidTacticGenConf.from_yaml(yaml_data)
        case OpenAIClientConf.ALIAS:
            return OpenAIClientConf.from_yaml(yaml_data)
        case _:
            raise ValueError(f"Unknown tactic conf: {attempted_alias}")
