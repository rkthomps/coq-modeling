import sys, os
import argparse
import subprocess


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Collect and save small portions of saved eval data."
    )
    parser.add_argument(
        "eval_dir", help="directory containig multiple evaluation subdirectories."
    )
    parser.add_argument(
        "sentence_db_loc", help="Location of the sentence database."
    )
    args = parser.parse_args(sys.argv[1:])
    assert isinstance(args.eval_dir, str)

    analysis_loc = os.path.join("src", "evaluation", "eval_analysis.py")
    for eval in os.listdir(args.eval_dir):
        eval_loc = os.path.join(args.eval_dir, eval)
        subprocess.run(["python3", analysis_loc, eval_loc, args.sentence_db_loc, "4"])
