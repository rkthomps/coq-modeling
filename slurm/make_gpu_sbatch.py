import sys, os
from pathlib import Path

import argparse
import yaml
from evaluation.evaluate import EvalConf

from model_deployment.tactic_gen_client import FidTacticGenConf, CodellamaTacticGenConf

RUN_MODEL_LOC = Path("./slurm/run-model.sh")
TACTIC_SERVER_LOC = Path("./src/model_deployment/tactic_gen_server.py")
GPU_SBATCH_LOC = Path("./slurm/run-gpus.sh")


def create_eval_proof_map(eval_conf: EvalConf) -> dict[int, tuple[str, int]]:
    pass


def get_eval_sbatch(eval_conf: EvalConf, n_tasks_per_node: int, n_nodes: int) -> str:
    match eval_conf.tactic_conf:
        case FidTacticGenConf():
            alias = "fid-local"
            checkpoint_loc = eval_conf.tactic_conf.checkpoint_loc
        case CodellamaTacticGenConf():
            alias = "local"
            checkpoint_loc = eval_conf.tactic_conf.checkpoint_loc
        case _:
            raise ValueError("Unsupported tactic configuration.")

    with RUN_MODEL_LOC.open("w") as fout:
        run_model_file = (
            "#!/bin/bash\n"
            f"python3 {TACTIC_SERVER_LOC} {alias} {checkpoint_loc} $SLURM_PROC_ID"
        )
        fout.write(run_model_file)

    server_sbatch = (
        "#!/bin/bash\n"
        f"#SBATCH -t {timeout}\n"
        f"#SBATCH --ntasks={n_tasks_per_node * n_nodes}\n"
        f"#SBATCH --nodes={n_nodes}\n"
        f"#SBATCH --ntasks-per-node={n_tasks_per_node}\n"
        f"#SBATCH --cpus-per-task=1\n"
        f"#SBATCH --gpus-per-task=1\n"
        f"srun -l {RUN_MODEL_LOC}\n"
    )

    with GPU_SBATCH_LOC.open("w") as fout:
        fout.write(server_sbatch)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("conf_loc", help="Location of eval configuration")
    parser.add_argument("n_tasks_per_node", help="Number of gpus per node")
    parser.add_argument("n_nodes", help="Number of nodes.")
    args = parser.parse_args(sys.argv[1:])

    conf_loc = Path(args.conf_loc)
    n_devices = args.n_devices
    n_nodes = args.n_nodes
    assert conf_loc.exists()
    assert isinstance(n_devices, int)
    assert isinstance(n_nodes, int)

    with conf_loc.open("r") as fin:
        conf = yaml.load(fin, Loader=yaml.Loader)

    eval_conf = EvalConf.from_yaml(conf)
