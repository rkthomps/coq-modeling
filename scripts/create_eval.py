import argparse
import os
import json
from pathlib import Path
from coqstoq import EvalTheorem
from coqstoq import get_theorem_list, Split
from coqstoq.check import EvalResults, Result
from util.coqstoq_utils import str2split


def get_thm_hash(thm: EvalTheorem) -> str:
    return f"{thm.project.workspace.name}/{thm.path}/{thm.theorem_start_pos.line}-{thm.theorem_start_pos.column}"


def load_eval_results(
    eval_loc: Path, hardware_desc: str, split: Split, coqstoq_loc: Path
) -> EvalResults:
    assert eval_loc.exists()
    all_results: dict[str, Result] = {}
    for eval_file in eval_loc.glob("**/*.json"):
        with open(eval_file, "r") as f:
            result_data = json.load(f)
            result = Result.from_json(result_data)
            all_results[get_thm_hash(result.thm)] = result

    coqstoq_thms = get_theorem_list(split, coqstoq_loc)
    if len(all_results) == len(coqstoq_thms):
        result_list: list[Result] = []
        for thm in coqstoq_thms:
            result_list.append(all_results[get_thm_hash(thm)])
        assert len(result_list) == len(coqstoq_thms)
        return EvalResults(hardware_desc, result_list)
    else:
        return EvalResults(hardware_desc, list(all_results.values()))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--eval_loc", type=str, required=True)
    parser.add_argument("--coqstoq_loc", type=str, required=True)
    parser.add_argument("--split", type=str, required=True)
    parser.add_argument("--hardware", type=str, required=True)
    parser.add_argument("--save_loc", type=str, required=True)
    args = parser.parse_args()

    eval_loc = Path(args.eval_loc)
    split = str2split(args.split)
    eval_results = load_eval_results(
        eval_loc, args.hardware, split, Path(args.coqstoq_loc)
    )

    save_loc = Path(args.save_loc)
    assert not save_loc.exists()
    os.makedirs(save_loc.parent, exist_ok=True)
    with save_loc.open("w") as fout:
        fout.write(json.dumps(eval_results.to_json(), indent=2))
