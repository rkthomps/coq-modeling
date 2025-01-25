import argparse
import json
import shutil

from pathlib import Path
from dataclasses import dataclass
from coqstoq import Split, EvalTheorem, get_theorem, get_theorem_list
from coqstoq.check import Result, EvalResults

from tactic_gen.lm_example import GeneralFormatterConf

from proof_retrieval.proof_retriever import SparseProofRetrieverConf
from proof_retrieval.proof_retriever import DeepProofRetrieverConf

from premise_selection.premise_client import SparseConf, SparseKind
from premise_selection.premise_filter import PROJ_THM_FILTER_CONF
from premise_selection.rerank_client import PremiseConf

from model_deployment.tactic_gen_client import TacticGenConf, DecoderTacticGenConf
from model_deployment.searcher import (
    SearcherConf,
    StraightLineSearcherConf,
    ClassicalSearchConf,
)
from model_deployment.run_proof import TestProofConf

from model_deployment.classical_searcher import ClassicalSuccess, ClassicalFailure
from model_deployment.prove import run_proof, RunProofConf, LocationInfo, RangoResult
from model_deployment.straight_line_searcher import (
    StraightLineSuccess,
    StraightLineFailure,
)
from model_deployment.whole_proof_searcher import (
    WholeProofSuccess,
    WholeProofFailure,
)
from model_deployment.tactic_gen_client import (
    TacticGenConf,
    tactic_conf_update_ips,
    tactic_gen_conf_from_yaml,
    tactic_gen_client_from_conf,
)
from model_deployment.conf_utils import (
    wait_for_servers,
    start_servers,
    tactic_gen_to_client_conf,
    StartModelCommand,
)

from util.util import get_basic_logger, clear_port_map, set_rango_logger

COQSTOQ_LOC = Path("CoqStoq")


def str2split(s: str) -> Split:
    match s:
        case "test":
            return Split.TEST
        case "val":
            return Split.VAL
        case "cutoff":
            return Split.CUTOFF
        case _:
            raise ValueError(
                f"Unknown split {s}. Available splits are 'test', 'val', 'cutoff'."
            )


def get_eval_thm(split: Split, idx: int) -> EvalTheorem:
    assert COQSTOQ_LOC.exists()
    return get_theorem(split, idx, COQSTOQ_LOC)


def get_data_loc(split: Split) -> Path:
    match split:
        case Split.TEST:
            p = Path("raw-data/coqstoq-test")
            assert p.exists()
            return p
        case Split.VAL:
            p = Path("raw-data/coqstoq-val")
            assert p.exists()
            return p
        case Split.CUTOFF:
            p = Path("raw-data/coqstoq-cutoff")
            assert p.exists()
            return p


def get_sentence_db_loc(split: Split) -> Path:
    match split:
        case Split.TEST:
            p = Path("raw-data/coqstoq-test/coqstoq-test-sentences.db")
            assert p.exists()
            return p
        case Split.VAL:
            p = Path("raw-data/coqstoq-val/coqstoq-val-sentences.db")
            assert p.exists()
            return p
        case Split.CUTOFF:
            p = Path("raw-data/coqstoq-cutoff/coqstoq-cutoff-sentences.db")
            assert p.exists()
            return p


def get_searcher_conf(model_alias: str) -> SearcherConf:
    timeout = 600
    straight_line_conf = StraightLineSearcherConf(
        timeout=timeout,
        print_proofs=True,
        initial_proof=None,
        token_mask=None,
    )

    match model_alias:
        case "rango-best-beam":
            return ClassicalSearchConf(
                max_branch=4,
                max_search_steps=1000000,
                depth_limit=30,
                timeout=600,
                beam_decode=True,
                initial_proof=None,
            )

        case "rango-best-rand":
            return ClassicalSearchConf(
                max_branch=4,
                max_search_steps=1000000,
                depth_limit=30,
                timeout=600,
                beam_decode=False,
                initial_proof=None,
            )

        case _:
            return straight_line_conf


def get_prefix_conf(model_alias: str, split: Split) -> TacticGenConf:
    assert model_alias == "prefix" or model_alias == "hybrid"
    model_loc = Path("models/deepseek-prefix-final")
    checkpoint = model_loc / "checkpoint-61000"
    checkpoint_loc = Path(checkpoint)

    match split:
        case Split.TEST:
            shutil.copy(
                model_loc / "test_conf.yaml",
                model_loc / "training_conf.yaml",
            )
        case Split.CUTOFF:
            shutil.copy(
                model_loc / "cutoff_conf.yaml",
                model_loc / "training_conf.yaml",
            )
        case Split.VAL:
            raise ValueError("Not supported in artifact. Doesn't appear in the paper.")

    formatter = GeneralFormatterConf(
        premise_client_conf=None,
        proof_retriever_conf=None,
        num_premises=None,
        num_proofs=None,
    )
    return DecoderTacticGenConf(Path(checkpoint), [formatter])


def get_tactic_confs(model_alias: str, split: Split) -> list[TacticGenConf]:
    data_loc = get_data_loc(split)
    sentence_db_loc = get_sentence_db_loc(split)

    tfidf_premise_conf = SparseConf(
        kind=SparseKind.TFIDF,
        context_format_alias="basic",
        premise_format_alias="basic",
        premise_filter_conf=PROJ_THM_FILTER_CONF,
        sentence_db_loc=sentence_db_loc,
        cached_premise_loc=None,
    )

    bm25_proof_conf = SparseProofRetrieverConf(
        kind="bm25",
        max_examples=20,
        data_loc=data_loc,
        sentence_db_loc=sentence_db_loc,
        cached_proof_loc=None,
        first_step_only=False,
    )

    match model_alias:
        case "rango" | "rango-best-beam" | "rango-best-rand":
            checkpoint = (
                "models/deepseek-bm25-proof-tfidf-proj-thm-prem-final/checkpoint-54500"
            )
            formatter = GeneralFormatterConf(
                premise_client_conf=tfidf_premise_conf,
                proof_retriever_conf=bm25_proof_conf,
                num_premises=50,
                num_proofs=20,
            )
            return [DecoderTacticGenConf(Path(checkpoint), [formatter])]

        case "rango-inter-file":
            checkpoint = (
                "models/deepseek-bm25-proof-tfidf-proj-thm-prem-random/checkpoint-54000"
            )
            formatter = GeneralFormatterConf(
                premise_client_conf=tfidf_premise_conf,
                proof_retriever_conf=bm25_proof_conf,
                num_premises=50,
                num_proofs=20,
            )
            return [DecoderTacticGenConf(Path(checkpoint), [formatter])]

        case "no-lemma":
            checkpoint = "models/deepseek-bm25-proof-final/checkpoint-56500"
            formatter = GeneralFormatterConf(
                premise_client_conf=None,
                proof_retriever_conf=bm25_proof_conf,
                num_premises=None,
                num_proofs=20,
            )
            return [DecoderTacticGenConf(Path(checkpoint), [formatter])]

        case "no-lemma-inter-file":
            checkpoint = "models/deepseek-bm25-proof-random/checkpoint-54000"
            formatter = GeneralFormatterConf(
                premise_client_conf=None,
                proof_retriever_conf=bm25_proof_conf,
                num_premises=None,
                num_proofs=20,
            )
            return [DecoderTacticGenConf(Path(checkpoint), [formatter])]

        case "no-proof":
            checkpoint = "models/deepseek-tfidf-proj-thm-prem-final/checkpoint-51500"
            formatter = GeneralFormatterConf(
                premise_client_conf=tfidf_premise_conf,
                proof_retriever_conf=None,
                num_premises=50,
                num_proofs=None,
            )
            return [DecoderTacticGenConf(Path(checkpoint), [formatter])]

        case "no-proof-inter-file":
            checkpoint = "models/deepseek-tfidf-proj-thm-prem-random/checkpoint-54000"
            formatter = GeneralFormatterConf(
                premise_client_conf=tfidf_premise_conf,
                proof_retriever_conf=None,
                num_premises=50,
                num_proofs=None,
            )
            return [DecoderTacticGenConf(Path(checkpoint), [formatter])]

        case "no-retrieval":
            checkpoint = "models/deepseek-basic-ablation/checkpoint-37500"
            formatter = GeneralFormatterConf(
                premise_client_conf=None,
                proof_retriever_conf=None,
                num_premises=None,
                num_proofs=None,
            )
            return [DecoderTacticGenConf(Path(checkpoint), [formatter])]

        case "no-retrieval-inter-file":
            checkpoint = "models/deepseek-basic-ablation-random/checkpoint-53500"
            formatter = GeneralFormatterConf(
                premise_client_conf=None,
                proof_retriever_conf=None,
                num_premises=None,
                num_proofs=None,
            )
            return [DecoderTacticGenConf(Path(checkpoint), [formatter])]

        case "first-step":
            checkpoint = "models/deepseek-bm25-first-step-proof-tfidf-proj-thm-prem-final/checkpoint-56000"
            first_step_proof_conf = SparseProofRetrieverConf(
                kind="bm25",
                max_examples=20,
                data_loc=data_loc,
                sentence_db_loc=sentence_db_loc,
                cached_proof_loc=None,
                first_step_only=True,
            )
            formatter = GeneralFormatterConf(
                premise_client_conf=tfidf_premise_conf,
                proof_retriever_conf=first_step_proof_conf,
                num_premises=50,
                num_proofs=20,
            )
            return [DecoderTacticGenConf(Path(checkpoint), [formatter])]

        case "tfidf-proof":
            checkpoint = "models/deepseek-proof-prem-final/checkpoint-45500"
            tfidf_proof_conf = SparseProofRetrieverConf(
                kind="tfidf",
                max_examples=20,
                data_loc=data_loc,
                sentence_db_loc=sentence_db_loc,
                cached_proof_loc=None,
                first_step_only=False,
            )
            formatter = GeneralFormatterConf(
                premise_client_conf=tfidf_premise_conf,
                proof_retriever_conf=tfidf_proof_conf,
                num_premises=50,
                num_proofs=20,
            )
            return [DecoderTacticGenConf(Path(checkpoint), [formatter])]

        case "codebert-proof":
            checkpoint = "models/deepseek-codebert-proof-tfidf-proj-thm-prem-final/checkpoint-57500"
            codebert_proof_conf = DeepProofRetrieverConf(
                model_name="microsoft/codebert-base",
                vector_db_loc=Path("data/test-codebert-proof-state-vector-db"),
                max_seq_len=512,
                max_num_proofs=20,
                data_loc=data_loc,
                sentence_db_loc=sentence_db_loc,
                first_step_only=False,
            )
            formatter = GeneralFormatterConf(
                premise_client_conf=tfidf_premise_conf,
                proof_retriever_conf=codebert_proof_conf,
                num_premises=50,
                num_proofs=20,
            )
            return [DecoderTacticGenConf(Path(checkpoint), [formatter])]

        case "prefix":
            return [get_prefix_conf(model_alias, split)]

        case "hybrid":
            prefix_conf = get_prefix_conf(model_alias, split)
            rango_checkpoint = (
                "models/deepseek-bm25-proof-tfidf-proj-thm-prem-final/checkpoint-54500"
            )
            rango_formatter = GeneralFormatterConf(
                premise_client_conf=tfidf_premise_conf,
                proof_retriever_conf=bm25_proof_conf,
                num_premises=50,
                num_proofs=20,
            )
            rango_conf = DecoderTacticGenConf(Path(rango_checkpoint), [rango_formatter])
            return [rango_conf, prefix_conf]

        case _:
            raise ValueError(f"Unknown model alias {model_alias}.")


def get_test_proof(model_alias: str, split: Split, idx: int) -> TestProofConf:
    eval_thm = get_eval_thm(split, idx)
    data_loc = get_data_loc(split)
    sentence_db_loc = get_sentence_db_loc(split)
    searcher_conf = get_searcher_conf(model_alias)
    tactic_confs = get_tactic_confs(model_alias, split)
    return TestProofConf(
        eval_thm,
        COQSTOQ_LOC,
        data_loc,
        sentence_db_loc,
        searcher_conf,
        tactic_confs,
        True,
        False,
    )


def get_results_loc(model_alias: str) -> list[Path]:
    results_locs = {
        "rango": [
            Path("results/rango.json"),
            Path("results/rango-cutoff.json"),
        ],
        "rango-inter-file": [
            Path("results/rango-abl-intersect-random.json"),
        ],
        "rango-best-beam": [
            Path("results/rango-abl-best-first-beam.json"),
        ],
        "rango-best-rand": [
            Path("results/rango-abl-best-first-temp.json"),
        ],
        "no-lemma": [
            Path("results/rango-abl-no-lemmas.json"),
            Path("results/rango-abl-intersect-no-lemma-final.json"),
        ],
        "no-lemma-inter-file": [
            Path("results/rango-abl-intersect-no-lemma-random.json"),
        ],
        "no-proof": [
            Path("results/rango-abl-no-proofs.json"),
            Path("results/rango-abl-intersect-no-proofs-final.json"),
        ],
        "no-proof-inter-file": [
            Path("results/rango-abl-intersect-no-proofs-random.json"),
        ],
        "no-retrieval": [
            Path("results/rango-abl-no-retrieval.json"),
            Path("results/rango-abl-intersect-no-retrieval-final.json"),
        ],
        "no-retrieval-inter-file": [
            Path("results/rango-abl-intersect-no-retrieval-random.json"),
        ],
        "first-step": [Path("results/rango-abl-first-step.json")],
        "tfidf-proof": [Path("results/rango-abl-tfidf.json")],
        "codebert-proof": [Path("results/rango-abl-codebert.json")],
        "prefix": [
            Path("results/rango-abl-prefix.json"),
            Path("results/rango-abl-prefix-cutoff.json"),
        ],
        "hybrid": [
            Path("results/rango-abl-prefix-hybrid.json"),
            Path("results/rango-abl-prefix-hybrid-cutoff.json"),
        ],
    }
    if model_alias not in results_locs:
        raise ValueError(f"No results found for {model_alias}.")
    return results_locs[model_alias]


def get_result(model_alias: str, thm: EvalTheorem) -> Result:
    results_locs = get_results_loc(model_alias)
    for results_loc in results_locs:
        with open(results_loc) as f:
            eval_data = json.load(f)
            results = EvalResults.from_json(eval_data)
            assert len(results.results)
        for r in results.results:
            if r.thm == thm:
                return r
    raise ValueError(f"Do not have a results for {model_alias}")


def get_orig_result(model_alias: str, split: Split, idx: int) -> Result:
    thm = get_theorem(split, idx, COQSTOQ_LOC)
    return get_result(model_alias, thm)


def print_info():
    print("Table 2:")
    print("  rango")
    print()
    print("Table 3:")
    print("  rango")
    print()
    print("Table 4:")
    print("  rango")
    print("  no-lemma")
    print("  no-proof")
    print("  no-retrieval")
    print()
    print("Table 5:")
    print("  rango")
    print("  no-lemma")
    print("  no-proof")
    print("  no-retrieval")
    print()
    print("Table 6:")
    print("  rango")
    print("  first-step")
    print()
    print("Table 7:")
    print("  rango")
    print("  tfidf-proof")
    print("  codebert-proof")
    print()
    print("Table 8:")
    print("  rango")
    print("  prefix")
    print("  hybrid")
    exit()


def print_result(theorem_list: list[EvalTheorem], result: Result):
    idx = theorem_list.index(result.thm)
    success_str = "Success" if result.proof is not None else "Failure"
    t = result.time
    assert t is not None
    print("{:6d}; {:7s}; {:5.1f}".format(idx, success_str, t))
    # print("{:3d}; {:7s}; {:04.1f}".format(idx, success_str, t))
    # print(f"{idx:3d}; {success_str:7s}; {t:4.1f}")


def print_avail_thms(alias: str, split: Split):
    results_locs = get_results_loc(alias)
    PRINT_NUM = 50
    num_printed = 0
    thms = get_theorem_list(split, COQSTOQ_LOC)
    for results_loc in results_locs:
        with results_loc.open("r") as fin:
            results_data = json.load(fin)
            results = EvalResults.from_json(results_data)
            for r in results.results:
                if r.thm.project.split != split.value:
                    continue
                print_result(thms, r)
                num_printed += 1
                if num_printed == PRINT_NUM:
                    return


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    subparsers = parser.add_subparsers(dest="command")

    preview_parser = subparsers.add_parser("preview")
    preview_parser.add_argument("alias")
    preview_parser.add_argument("split")

    info_parser = subparsers.add_parser("info")

    run_parser = subparsers.add_parser("run")
    run_parser.add_argument("alias")
    run_parser.add_argument("split")
    run_parser.add_argument("idx", type=int)

    eval_parser = subparsers.add_parser("eval")
    eval_parser.add_argument("alias")
    eval_parser.add_argument("split")

    args = parser.parse_args()
    if args.command == "info":
        print_info()
        exit()

    elif args.command == "preview":
        coqstoq_split = str2split(args.split)
        print_avail_thms(args.alias, coqstoq_split)
        exit()

    assert args.command == "run" or args.command == "eval"
    coqstoq_split = str2split(args.split)

    if args.command == "run":
        conf = get_test_proof(args.alias, coqstoq_split, args.idx)
        print(conf.thm.project.dir_name, conf.thm.path)
        orig_result = get_orig_result(args.alias, coqstoq_split, args.idx)
        print("Original Proof:")
        print(orig_result.proof)
        print("Original Time:")
        print(orig_result.time)
    else:
        assert args.command == "eval"
        conf = get_test_proof(args.alias, coqstoq_split, 0)

    # Example: 37
    print("\n\n Loading model...")
    clean_tactic_confs: list[TacticGenConf] = []
    all_commands: list[StartModelCommand] = []
    next_num = 0
    for tactic_conf in conf.tactic_confs:
        clean_tactic_conf, n_commands, commands = tactic_gen_to_client_conf(
            tactic_conf, next_num
        )
        all_commands.extend(commands)
        clean_tactic_confs.append(clean_tactic_conf)
        next_num = n_commands

    procs = []
    if 0 < len(all_commands):
        clear_port_map()
        procs = start_servers(all_commands)
        port_map = wait_for_servers(next_num)
        for tactic_conf in clean_tactic_confs:
            tactic_conf_update_ips(tactic_conf, port_map)

    conf.tactic_confs = clean_tactic_confs

    if args.command == "run":
        orig_result = get_orig_result(args.alias, coqstoq_split, args.idx)
        try:
            result = run_proof(conf.to_run_conf())
            match result:
                case ClassicalSuccess():
                    print(
                        f"\n\n ORIGINAL RESULT: {'SUCCESS' if orig_result.proof is not None else 'FAILURE'}"
                    )
                    print(f"ORIGINAL TIME: {orig_result.time}")
                    print(f"ORIGINAL PROOF: {orig_result.proof}")
                    print("CURRENT RESULT: SUCCESS")
                    print(f"CURRENT TIME: {result.time}")
                    print(f"CURRENT PROOF:")
                    print(result.successful_candidate.proof_str)

                case ClassicalFailure():
                    print("failed")
                case StraightLineSuccess():
                    print(
                        f"\n\nORIGINAL RESULT: {'SUCCESS' if orig_result.proof is not None else 'FAILURE'}"
                    )
                    print(f"ORIGINAL TIME: {orig_result.time}")
                    print(f"ORIGINAL PROOF: {orig_result.proof}")
                    print("CURRENT RESULT: SUCCESS")
                    print(f"CURRENT TIME: {result.time}")
                    print(f"CURRENT PROOF:")
                    print(result.successful_proof.proof_text_to_string())

                case StraightLineFailure():
                    print("failed")
                case WholeProofSuccess():
                    print(result.successful_proof.proof_text_to_string())
                case WholeProofFailure():
                    print("failed")
        finally:
            for p in procs:
                p.kill()

    else:
        assert args.command == "eval"
        theorem_list = get_theorem_list(coqstoq_split, COQSTOQ_LOC)
        results: list[Result] = []
        for thm in theorem_list[37:]:
            thm_conf = TestProofConf(
                thm,
                conf.coqstoq_loc,
                conf.data_loc,
                conf.sentence_db_loc,
                conf.search_conf,
                conf.tactic_confs,
                conf.print_proofs,
                conf.print_trees,
            )
            try:
                search_result = run_proof(thm_conf.to_run_conf())
                result = RangoResult.from_search_result(thm, search_result)
                results.append(result)
            finally:
                for p in procs:
                    p.kill()
