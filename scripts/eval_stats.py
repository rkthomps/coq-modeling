import sys, os
import argparse
from pathlib import Path
from model_deployment.run_proofs import SearchSummary, load_results


parser = argparse.ArgumentParser()
parser.add_argument("eval_loc")
args = parser.parse_args(sys.argv[1:])

summaries = load_results(Path(args.eval_loc))


def count_num_correct(summaries: list[SearchSummary]) -> int:
    num_correct = 0
    for summary in summaries:
        if summary.success:
            num_correct += 1
    return num_correct


print("Num attempts: ", len(summaries))
print("Num correct:", count_num_correct(summaries))
