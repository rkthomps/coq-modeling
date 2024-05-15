import sys, os
import csv
import argparse
from pathlib import Path
from model_deployment.prove import Summary, SearchSummary, MCTSSummary
from model_deployment.run_proofs import SearchSummary, load_results


def count_num_correct(summaries: list[Summary]) -> int:
    num_correct = 0
    for summary in summaries:
        if summary.success:
            num_correct += 1
    return num_correct

def create_csv(results_loc: Path, summaries: list[Summary]):
    sorted_summaries = sorted(summaries)
    if 0 == len(sorted_summaries):
        print("Nothing to write.", file=sys.stderr)

    with results_loc.open("w", newline="") as fout:
        field_names, _ = sorted_summaries[0].to_csv_dict()
        writer = csv.DictWriter(fout, field_names)
        writer.writeheader()
        for r in sorted_summaries:
            _, r_dict = r.to_csv_dict()
            writer.writerow(r_dict)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("eval_loc")
    args = parser.parse_args(sys.argv[1:])
    eval_loc = Path(args.eval_loc)
    assert eval_loc.exists()

    summaries = load_results(eval_loc)
    num_correct = count_num_correct(summaries)
    num_attempted = len(summaries)
    results_loc = eval_loc / "results.csv"
    print(f"Num Correct {num_correct}; Num Attempted {num_attempted}; Saved to {results_loc}.")


