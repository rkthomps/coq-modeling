import os
import shutil
import sys
import argparse
import yaml
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("eval_conf_loc")
args = parser.parse_args(sys.argv[1:])

with open(args.eval_conf_loc, "r") as fin:
    conf = yaml.load(fin, Loader=yaml.Loader)

results_loc = conf["results_loc"]
if os.path.exists(results_loc):
    response = input(f"Results exists in {results_loc}. Continue?: ")
    if not response.lower().startswith("y"):
        raise FileExistsError(f"{results_loc}")
else:
    os.makedirs(results_loc)
    shutil.copy(args.eval_conf_loc, results_loc)

std_out_loc = os.path.join(conf["results_loc"], "out.txt")
std_err_loc = os.path.join(conf["results_loc"], "err.txt")
evaluate_loc = os.path.join("src", "evaluation", "evaluate.py")
args = ["python3", evaluate_loc, args.eval_conf_loc]
with open(std_out_loc, "a") as new_std_out, open(std_err_loc, "a") as new_std_err:
    subprocess.run(args, stdout=new_std_out, stderr=new_std_err)
