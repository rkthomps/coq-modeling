from typing import Optional
import argparse
import re
import json
import pandas as pd
import statistics
from tqdm import tqdm
from pathlib import Path
from dataclasses import dataclass
from data_management.dataset_file import DPCache
from data_management.sentence_db import SentenceDB
from data_management.splits import DataSplit, Split
from evaluation.find_coqstoq_idx import get_thm_desc

from coqstoq import Split as CQSplit, get_theorem_list, EvalTheorem
from coqstoq.check import EvalResults, Result
from edist.sed import standard_sed


# --------------------------------
# REPLICATION CODE FOR TABLE 1
# --------------------------------
@dataclass
class CountResult:
    proof_step_count: list[int]
    num_proofs_count: list[int]

    @property
    def num_repos(self):
        return len(self.num_proofs_count)

    @property
    def num_proofs(self):
        option1 = sum(self.num_proofs_count)
        option2 = len(self.proof_step_count)
        assert option1 == option2
        return option1

    @property
    def num_steps(self):
        return sum(self.proof_step_count)

    def save(self, steps_loc: Path, proofs_loc: Path):
        with steps_loc.open("w") as f:
            json.dump(self.proof_step_count, f)
        with proofs_loc.open("w") as f:
            json.dump(self.num_proofs_count, f)


def get_training_proof_step_counts(
    split: DataSplit, data_loc: Path, sentence_db: SentenceDB
) -> CountResult:
    proof_step_counts: list[int] = []
    num_proofs_count: dict[str, int] = {}
    for f_info in tqdm(split.get_file_list(Split.TRAIN)):
        proofs = f_info.get_proofs(data_loc, sentence_db)
        for proof in proofs:
            proof_step_counts.append(len(proof.steps))
        if f_info.repository not in num_proofs_count:
            num_proofs_count[f_info.repository] = 0
        num_proofs_count[f_info.repository] += len(proofs)
    return CountResult(proof_step_counts, list(num_proofs_count.values()))


def get_coqstoq_proof_counts(
    coqstoq_loc: Path, coqstoq_split: CQSplit, data_loc: Path, sentence_db: SentenceDB
) -> CountResult:
    coqstoq_thms = get_theorem_list(coqstoq_split, coqstoq_loc)
    proof_step_counts: list[int] = []
    num_proofs_count: dict[str, int] = {}
    dp_cache = DPCache()
    for thm in tqdm(coqstoq_thms):
        thm_desc = get_thm_desc(thm, data_loc, sentence_db, dp_cache=dp_cache)
        assert thm_desc is not None
        proof_step_counts.append(len(thm_desc.dp.proofs[thm_desc.idx].steps))
        if thm.project.dir_name not in num_proofs_count:
            num_proofs_count[thm.project.dir_name] = 0
        num_proofs_count[thm.project.dir_name] += 1
    return CountResult(proof_step_counts, list(num_proofs_count.values()))


def replicate_tab1():
    print("Getting training counts...")
    SPLIT_LOC = Path("splits/official-split-icse.json")
    TRAINING_DATA_LOC = Path("raw-data/coq-dataset")
    TRAINING_SENTENCE_DB_LOC = Path("raw-data/coq-dataset/sentences.db")
    training_sdb = SentenceDB.load(TRAINING_SENTENCE_DB_LOC)
    training_split = DataSplit.load(SPLIT_LOC)
    training_results = get_training_proof_step_counts(
        training_split, TRAINING_DATA_LOC, training_sdb
    )

    print("Getting val counts...")
    COQSTOQ_LOC = Path("CoqStoq").resolve()
    assert COQSTOQ_LOC.exists()
    COQSTOQ_VAL_LOC = Path("raw-data/coqstoq-val")
    COQSTOQ_VAL_SDB_LOC = Path("raw-data/coqstoq-val/coqstoq-val-sentences.db")
    val_sdb = SentenceDB.load(COQSTOQ_VAL_SDB_LOC)
    val_results = get_coqstoq_proof_counts(
        COQSTOQ_LOC, CQSplit.VAL, COQSTOQ_VAL_LOC, val_sdb
    )

    print("Gettting test counts...")
    COQSTOQ_TEST_LOC = Path("raw-data/coqstoq-test")
    COQSTOQ_TEST_SDB_LOC = Path("raw-data/coqstoq-test/coqstoq-test-sentences.db")
    test_sdb = SentenceDB.load(COQSTOQ_TEST_SDB_LOC)
    test_results = get_coqstoq_proof_counts(
        COQSTOQ_LOC, CQSplit.TEST, COQSTOQ_TEST_LOC, test_sdb
    )

    df = pd.DataFrame(
        {
            "Training": [
                training_results.num_repos,
                training_results.num_proofs,
                training_results.num_steps,
            ],
            "Validation": [
                val_results.num_repos,
                val_results.num_proofs,
                val_results.num_steps,
            ],
            "Test": [
                test_results.num_repos,
                test_results.num_proofs,
                test_results.num_steps,
            ],
            "Total": [
                training_results.num_repos
                + val_results.num_repos
                + test_results.num_repos,
                training_results.num_proofs
                + val_results.num_proofs
                + test_results.num_proofs,
                training_results.num_steps
                + val_results.num_steps
                + test_results.num_steps,
            ],
        },
        index=["Repositories", "Proofs", "Proof Steps"],
    )
    print(df)


# --------------------------------
# REPLICATION CODE FOR TABLE 2
# --------------------------------
@dataclass
class NamedDF:
    name: str
    df: pd.DataFrame


def results_to_df(results: EvalResults, sysname: str, timeout: int = 600) -> NamedDF:
    rows = []
    for result in results.results:
        rows.append(
            {
                "project": result.thm.project.workspace.name,
                "path": result.thm.path,
                "line": result.thm.theorem_start_pos.line,
                "success": result.proof is not None
                and result.time is not None
                and result.time < timeout,
                "time": result.time,
            }
        )
    df = pd.DataFrame(rows)
    return NamedDF(sysname, df.set_index(["project", "path", "line"]))


def create_joint_eval(
    df1: NamedDF, df2: NamedDF, normalize: bool = True, timeout: int = 600
) -> NamedDF:
    if normalize:
        new_name = f"Adjusted {df1.name} + {df2.name}"
    else:
        new_name = f"Unadjusted {df1.name} + {df2.name}"
    merged_df = df1.df.merge(
        df2.df, left_index=True, right_index=True, how="outer", suffixes=("_1", "_2")
    )
    if normalize:
        merged_df["time"] = merged_df.apply(
            lambda row: min(row["time_1"], row["time_2"]) * 2, axis=1
        )
    else:
        merged_df["time"] = merged_df.apply(
            lambda row: min(row["time_1"], row["time_2"]), axis=1
        )
    merged_df["success"] = (merged_df["success_1"] | merged_df["success_2"]) & (
        merged_df["time"] < timeout
    )
    return NamedDF(new_name, merged_df[["success", "time"]])


def filter_df(named_df: NamedDF, idx: pd.Index) -> NamedDF:
    return NamedDF(named_df.name, named_df.df.loc[idx])


def get_by_project_summary(named_df: NamedDF) -> pd.DataFrame:
    return (
        named_df.df.groupby("project")
        .agg(
            RATE=("success", "mean"),
            SUCCESSES=("success", "sum"),
            TOTAL=("success", "count"),
        )
        .sort_values("TOTAL", ascending=False)
    )


def get_totals(named_df: NamedDF) -> pd.Series:
    n_df = NamedDF(
        named_df.name,
        named_df.df.agg(
            RATE=("success", "mean"),
            SUCCESSES=("success", "sum"),
            TOTAL=("success", "count"),
        ),
    )
    series = n_df.df["success"]
    series.name = named_df.name
    return series


def load_eval_result(p: Path) -> EvalResults:
    with p.open("r") as f:
        data = json.load(f)
        return EvalResults.from_json(data)


def replicate_tab2():
    RANGO_RESULTS_LOC = Path("results/rango.json")
    TACTICIAN_RESULTS_LOC = Path("results/tactician.json")
    PROVERBOT_RESULTS_LOC = Path("results/proverbot.json")
    GRAPH2TAC_RESULTS_LOC = Path("results/graph2tac.json")

    ## Coqstoq eval (table 1 left)
    rango_results = load_eval_result(RANGO_RESULTS_LOC)
    tactician_results = load_eval_result(TACTICIAN_RESULTS_LOC)
    proverbot_results = load_eval_result(PROVERBOT_RESULTS_LOC)

    assert len(rango_results.results) == len(tactician_results.results)
    assert len(rango_results.results) == len(proverbot_results.results)

    rango_df = results_to_df(rango_results, "Rango")
    tactician_df = results_to_df(tactician_results, "Tactician")
    proverbot_df = results_to_df(proverbot_results, "Proverbot")

    rango_project_df = get_by_project_summary(rango_df)
    tactician_project_df = get_by_project_summary(tactician_df)
    proverbot_project_df = get_by_project_summary(proverbot_df)

    rango_final_series = get_totals(rango_df)
    tactician_final_series = get_totals(tactician_df)
    proverbot_final_series = get_totals(proverbot_df)

    table2_part_1_project = pd.concat(
        [rango_project_df, tactician_project_df, proverbot_project_df],
        keys=["Rango", "Tactician", "Proverbot"],
        axis=1,
    )
    print("Table 2 (left) by project")
    print(table2_part_1_project)

    table2_part1_total = pd.concat(
        [rango_final_series, tactician_final_series, proverbot_final_series], axis=1
    )
    print("\nTable 2 (left) totals")
    print(table2_part1_total)

    combined_rango_tactician_df = create_joint_eval(
        rango_df, tactician_df, normalize=False
    )
    combined_rango_proverbot_df = create_joint_eval(
        rango_df, proverbot_df, normalize=False
    )
    table2_part1_combined = pd.concat(
        [
            get_totals(combined_rango_tactician_df),
            get_totals(combined_rango_proverbot_df),
        ],
        axis=1,
    )
    print("\nTable 2 (left) combined")
    print(table2_part1_combined)

    graph2tac_results = load_eval_result(GRAPH2TAC_RESULTS_LOC)
    graph2tac_df = results_to_df(graph2tac_results, "Graph2Tac")
    filtered_rango = filter_df(rango_df, graph2tac_df.df.index)
    rango_project_df = get_by_project_summary(filtered_rango)
    graph2tac_project_df = get_by_project_summary(graph2tac_df)

    table2_part2_project = pd.concat(
        [rango_project_df, graph2tac_project_df],
        keys=["Rango", "Graph2Tac"],
        axis=1,
    )
    print("\nTable 2 (right) by project")
    print(table2_part2_project)

    table2_part2_total = pd.concat(
        [get_totals(filtered_rango), get_totals(graph2tac_df)], axis=1
    )
    print("\nTable 2 (right) totals")
    print(table2_part2_total)

    combined_rango_graph2tac_df = create_joint_eval(
        filtered_rango, graph2tac_df, normalize=False
    )
    table2_part2_combined = pd.concat([get_totals(combined_rango_graph2tac_df)], axis=1)
    print("\nTable 2 (right) combined")
    print(table2_part2_combined)


# --------------------------------
# REPLICATION CODE FOR TABLE 3
# --------------------------------
def replicate_tab3():
    RANGO_RESULTS_LOC = Path("results/rango-cutoff.json")
    TACTICIAN_RESULTS_LOC = Path("results/tactician-cutoff.json")
    PROVERBOT_RESULTS_LOC = Path("results/proverbot-cutoff.json")

    rango_results = load_eval_result(RANGO_RESULTS_LOC)
    tactician_results = load_eval_result(TACTICIAN_RESULTS_LOC)
    proverbot_results = load_eval_result(PROVERBOT_RESULTS_LOC)

    assert len(rango_results.results) == len(tactician_results.results)
    assert len(rango_results.results) == len(proverbot_results.results)

    rango_df = results_to_df(rango_results, "Rango")
    tactician_df = results_to_df(tactician_results, "Tactician")
    proverbot_df = results_to_df(proverbot_results, "Proverbot")

    rango_project_df = get_by_project_summary(rango_df)
    tactician_project_df = get_by_project_summary(tactician_df)
    proverbot_project_df = get_by_project_summary(proverbot_df)

    table3_project = pd.concat(
        [rango_project_df, tactician_project_df, proverbot_project_df],
        keys=["Rango", "Tactician", "Proverbot"],
        axis=1,
    )
    print("Table 3 by project")
    print(table3_project)

    rango_final_series = get_totals(rango_df)
    tactician_final_series = get_totals(tactician_df)
    proverbot_final_series = get_totals(proverbot_df)

    table3_total = pd.concat(
        [rango_final_series, tactician_final_series, proverbot_final_series], axis=1
    )
    print("\nTable 3 totals")
    print(table3_total)


# --------------------------------
# REPLICATION CODE FOR TABLE 4
# --------------------------------
def get_thm_hash(thm: EvalTheorem) -> str:
    return f"{thm.project.workspace.name}/{thm.path}/{thm.theorem_start_pos.line}-{thm.theorem_start_pos.column}"


def same_thms(result_list: list[EvalResults]) -> bool:
    if len(result_list) == 0:
        return True
    first_thms = set([get_thm_hash(r.thm) for r in result_list[0].results])
    for result in result_list[1:]:
        thms = set([get_thm_hash(r.thm) for r in result.results])
        if thms != first_thms:
            return False
    return True


def replicate_tab4():
    RANGO_RESULTS_LOC = Path("results/rango.json")
    RANGO_NO_LEMMAS_LOC = Path("results/rango-abl-no-lemmas.json")
    RANGO_NO_PROOFS_LOC = Path("results/rango-abl-no-proofs.json")
    RANGO_NO_RETRIEVAL_LOC = Path("results/rango-abl-no-retrieval.json")

    rango_results = load_eval_result(RANGO_RESULTS_LOC)
    rango_no_lemmas_results = load_eval_result(RANGO_NO_LEMMAS_LOC)
    rango_no_proofs_results = load_eval_result(RANGO_NO_PROOFS_LOC)
    rango_no_retrieval_results = load_eval_result(RANGO_NO_RETRIEVAL_LOC)

    assert same_thms(
        [rango_no_lemmas_results, rango_no_proofs_results, rango_no_retrieval_results]
    )
    rango_df = results_to_df(rango_results, "Rango")
    rango_no_lemmas_df = results_to_df(rango_no_lemmas_results, "Rango No Lemmas")
    rango_no_proofs_df = results_to_df(rango_no_proofs_results, "Rango No Proofs")
    rango_no_retrieval_df = results_to_df(
        rango_no_retrieval_results, "Rango No Retrieval"
    )
    filtered_rango = filter_df(rango_df, rango_no_lemmas_df.df.index)

    total_df = pd.concat(
        [
            get_totals(filtered_rango),
            get_totals(rango_no_lemmas_df),
            get_totals(rango_no_proofs_df),
            get_totals(rango_no_retrieval_df),
        ],
        axis=1,
    )
    print("Table 4")
    print(total_df)


# --------------------------------
# REPLICATION CODE FOR TABLE 5
# --------------------------------
def replicate_tab5():
    RANGO_LOC = Path("results/rango.json")
    names = [
        ("Rango (Inter-file)", Path("results/rango-abl-intersect-random.json")),
        ("Rango No Lemmas", Path("results/rango-abl-intersect-no-lemma-final.json")),
        (
            "Rango No Lemmas (Inter-file)",
            Path("results/rango-abl-intersect-no-lemma-random.json"),
        ),
        ("Rango No Proofs", Path("results/rango-abl-intersect-no-proofs-final.json")),
        (
            "Rango No Proofs (Inter-file)",
            Path("results/rango-abl-intersect-no-proofs-random.json"),
        ),
        (
            "Rango No Retrieval",
            Path("results/rango-abl-intersect-no-retrieval-final.json"),
        ),
        (
            "Rango No Retrieval (Inter-file)",
            Path("results/rango-abl-intersect-no-retrieval-random.json"),
        ),
    ]

    totals: list[pd.Series] = []
    filter_idx: Optional[pd.Index] = None
    for name, loc in names:
        results = load_eval_result(loc)
        df = results_to_df(results, name)
        filter_idx = df.df.index
        total = get_totals(df)
        totals.append(total)

    assert filter_idx is not None
    rango_results = load_eval_result(RANGO_LOC)
    rango_df = results_to_df(rango_results, "Rango")
    rango_df = filter_df(rango_df, filter_idx)
    total = get_totals(rango_df)
    totals.insert(0, total)

    total_df = pd.concat(totals, axis=1)
    print("Table 5")
    print(total_df)


# --------------------------------
# REPLICATION CODE FOR TABLE 6
# --------------------------------
def replicate_tab6():
    RANGO_RESULTS_LOC = Path("results/rango.json")
    RANGO_FIRST_STEP_LOC = Path("results/rango-abl-first-step.json")

    rango_results = load_eval_result(RANGO_RESULTS_LOC)
    rango_first_step_results = load_eval_result(RANGO_FIRST_STEP_LOC)

    rango_df = results_to_df(rango_results, "Every Proof Step")
    rango_first_step_df = results_to_df(rango_first_step_results, "Only First Step")
    rango_df = filter_df(rango_df, rango_first_step_df.df.index)

    total_df = pd.concat(
        [get_totals(rango_df), get_totals(rango_first_step_df)], axis=1
    )

    print("Table 6")
    print(total_df)


# --------------------------------
# REPLICATION CODE FOR TABLE 7
# --------------------------------
def replicate_tab7():
    RANGO_RESULTS_LOC = Path("results/rango.json")
    TFIDF_RESULTS_LOC = Path("results/rango-abl-tfidf.json")
    CODEBERT_RESULTS_LOC = Path("results/rango-abl-codebert.json")

    rango_results = load_eval_result(RANGO_RESULTS_LOC)
    tfidf_results = load_eval_result(TFIDF_RESULTS_LOC)
    codebert_results = load_eval_result(CODEBERT_RESULTS_LOC)

    rango_df = results_to_df(rango_results, "Rango")
    tfidf_df = results_to_df(tfidf_results, "TF-IDF")
    codebert_df = results_to_df(codebert_results, "CodeBERT")

    total_df = pd.concat(
        [get_totals(rango_df), get_totals(tfidf_df), get_totals(codebert_df)], axis=1
    )

    print("Table 7")
    print(total_df)


# --------------------------------
# REPLICATION CODE FOR TABLE 8
# --------------------------------
def replicate_tab8():
    RANGO_RESULTS_LOC = Path("results/rango.json")
    PREFIX_RESULTS_LOC = Path("results/rango-abl-prefix.json")
    HYBRID_RESULTS_LOC = Path("results/rango-abl-prefix-hybrid.json")

    rango_results = load_eval_result(RANGO_RESULTS_LOC)
    prefix_results = load_eval_result(PREFIX_RESULTS_LOC)
    hybrid_results = load_eval_result(HYBRID_RESULTS_LOC)

    rango_df = results_to_df(rango_results, "Rango")
    prefix_df = results_to_df(prefix_results, "Prefix")
    hybrid_df = results_to_df(hybrid_results, "Hybrid")

    total_df = pd.concat(
        [get_totals(rango_df), get_totals(prefix_df), get_totals(hybrid_df)], axis=1
    )

    print("Table 8 (CoqStoq Test Set)")
    print(total_df)

    RANGO_CUTOFF_RESULTS_LOC = Path("results/rango-cutoff.json")
    PREFIX_CUTOFF_RESULTS_LOC = Path("results/rango-abl-prefix-cutoff.json")
    HYBRID_CUTOFF_RESULTS_LOC = Path("results/rango-abl-prefix-hybrid-cutoff.json")

    rango_cutoff_results = load_eval_result(RANGO_CUTOFF_RESULTS_LOC)
    prefix_cutoff_results = load_eval_result(PREFIX_CUTOFF_RESULTS_LOC)
    hybrid_cutoff_results = load_eval_result(HYBRID_CUTOFF_RESULTS_LOC)

    rango_cutoff_df = results_to_df(rango_cutoff_results, "Rango")
    prefix_cutoff_df = results_to_df(prefix_cutoff_results, "Prefix")
    hybrid_cutoff_df = results_to_df(hybrid_cutoff_results, "Hybrid")

    total_cutoff_df = pd.concat(
        [
            get_totals(rango_cutoff_df),
            get_totals(prefix_cutoff_df),
            get_totals(hybrid_cutoff_df),
        ],
        axis=1,
    )

    print("\nTable 8 (CoqStoq Cutoff Set)")
    print(total_cutoff_df)


# --------------------------------
# REPLICATION CODE FOR TABLE 9
# --------------------------------
def replicate_tab9():
    RANGO_RESULTS_LOC = Path("results/rango.json")
    BEAM_RESULTS_LOC = Path("results/rango-abl-best-first-beam.json")
    TEMP_RESULTS_LOC = Path("results/rango-abl-best-first-temp.json")

    rango_results = load_eval_result(RANGO_RESULTS_LOC)
    beam_results = load_eval_result(BEAM_RESULTS_LOC)
    temp_results = load_eval_result(TEMP_RESULTS_LOC)

    rango_df = results_to_df(rango_results, "Rango")
    beam_df = results_to_df(beam_results, "Beam")
    temp_df = results_to_df(temp_results, "Temp")
    rango_df = filter_df(rango_df, beam_df.df.index)

    total_df = pd.concat(
        [get_totals(rango_df), get_totals(beam_df), get_totals(temp_df)], axis=1
    )

    print("Table 9")
    print(total_df)


# --------------------------------
# REPLICATION CODE FOR TABLE 10
# --------------------------------
def load_results(loc: Path) -> EvalResults:
    with loc.open() as fin:
        eval_data = json.load(fin)
        return EvalResults.from_json(eval_data)


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


def find_mutual_proofs(
    results_list: list[EvalResults], timeout: int = 600
) -> list[int]:
    all_succeed_indices: list[int] = []
    assert 0 < len(results_list)
    results_num = len(results_list[0].results)
    for i in range(results_num):
        all_succeed = True
        for r_list in results_list:
            assert i < len(r_list.results)
            result_i = r_list.results[i]
            if (
                result_i.proof is None
                or result_i.time is None
                or timeout <= result_i.time
            ):
                all_succeed = False
                break
        if all_succeed:
            all_succeed_indices.append(i)
    return all_succeed_indices


def get_proof_lengths(eval: EvalResults, indices: list[int]) -> list[int]:
    proof_lengths: list[int] = []
    for i in indices:
        assert i < len(eval.results)
        result_i = eval.results[i]
        assert result_i.proof is not None
        proof_lengths.append(proof_length(result_i.proof))
    return proof_lengths


def get_edists(
    eval: EvalResults, human_eval: EvalResults, indices: list[int]
) -> list[float]:
    edists: list[float] = []
    for i in indices:
        assert i < len(eval.results)
        result_i = eval.results[i]
        assert i < len(human_eval.results)
        human_i = human_eval.results[i]
        assert result_i.proof is not None
        assert human_i.proof is not None
        edists.append(fair_edist(result_i.proof, human_i.proof) * 1.0)
    return edists


def replicate_tab10():
    HUMAN_EVAL_LOC = Path("results/human.json")
    RANGO_EVAL_LOC = Path("results/rango.json")
    TACTICIAN_EVAL_LOC = Path("results/tactician.json")
    PROVERBOT_EVAL_LOC = Path("results/proverbot.json")

    human_eval = load_results(HUMAN_EVAL_LOC)
    rango_eval = load_results(RANGO_EVAL_LOC)
    tactician_eval = load_results(TACTICIAN_EVAL_LOC)
    proverbot_eval = load_results(PROVERBOT_EVAL_LOC)

    mutual_idxs = find_mutual_proofs([rango_eval, tactician_eval, proverbot_eval])
    human_lengths = get_proof_lengths(human_eval, mutual_idxs)
    rango_lengths = get_proof_lengths(rango_eval, mutual_idxs)
    tactician_lengths = get_proof_lengths(tactician_eval, mutual_idxs)
    proverbot_lengths = get_proof_lengths(proverbot_eval, mutual_idxs)

    print("PROOF LENGTHS")
    print(
        "Human",
        "mean:",
        statistics.mean(human_lengths),
        "median:",
        statistics.median(human_lengths),
    )
    print(
        "Rango",
        "mean:",
        statistics.mean(rango_lengths),
        "median:",
        statistics.median(rango_lengths),
    )
    print(
        "Tactician",
        "mean:",
        statistics.mean(tactician_lengths),
        "median:",
        statistics.median(tactician_lengths),
    )
    print(
        "Proverbot",
        "mean:",
        statistics.mean(proverbot_lengths),
        "median:",
        statistics.median(proverbot_lengths),
    )

    mutual_idxs = find_mutual_proofs([rango_eval, tactician_eval, proverbot_eval])
    rango_edists = get_edists(rango_eval, human_eval, mutual_idxs)
    tactician_edists = get_edists(tactician_eval, human_eval, mutual_idxs)
    proverbot_edists = get_edists(proverbot_eval, human_eval, mutual_idxs)

    print("\nEDIST")
    print(
        "Rango",
        "mean:",
        statistics.mean(rango_edists),
        "median:",
        statistics.median(rango_edists),
    )
    print(
        "Tactician",
        "mean:",
        statistics.mean(tactician_edists),
        "median:",
        statistics.median(tactician_edists),
    )
    print(
        "Proverbot",
        "mean:",
        statistics.mean(proverbot_edists),
        "median:",
        statistics.median(proverbot_edists),
    )


def replicate_fig2():
    pass


def replicate_fig3():
    pass


def replicate_fig4():
    pass


def replicate_fig5():
    pass


def replicate_fig6():
    pass


OPTIONS = {
    "tab1": replicate_tab1,
    "tab2": replicate_tab2,
    "tab3": replicate_tab3,
    "tab4": replicate_tab4,
    "tab5": replicate_tab5,
    "tab6": replicate_tab6,
    "tab7": replicate_tab7,
    "tab8": replicate_tab8,
    "tab9": replicate_tab9,
    "tab10": replicate_tab10,
    "fig2": replicate_fig2,
    "fig3": replicate_fig3,
    "fig4": replicate_fig4,
    "fig5": replicate_fig5,
    "fig6": replicate_fig6,
}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Replicate Rango Results.")

    for k, _ in OPTIONS.items():
        parser.add_argument(f"--{k}", action="store_true", help=f"Replicate {k}")

    args = parser.parse_args()

    for k, v in args.__dict__.items():
        if v:
            OPTIONS[k]()
            break
