from __future__ import annotations
from typing import Optional
import pickle
import sys, os
import subprocess
import requests
import json
from typing import Any
from pathlib import Path
from dataclasses import dataclass
from datetime import datetime
from tqdm import tqdm

import argparse
import yaml
from model_deployment.conf_utils import (
    merge,
    to_client_conf,
    TopLevelConf,
    StartModelCommand,
)
from evaluation.evaluate import EvalConf
from data_management.splits import Split, split2str, DataSplit, FileInfo
from data_management.sentence_db import SentenceDB

from model_deployment.tactic_gen_client import FidTacticGenConf, CodellamaTacticGenConf
from util.constants import CLEAN_CONFIG, SERVER_LOC
from util.socket_client import ServerAdapter

RUN_MODELS_LOC = Path("./jobs/run-models.sh")
TACTIC_SERVER_LOC = Path("./src/model_deployment/tactic_gen_server.py")
GPU_SBATCH_LOC = Path("./jobs/run-gpus.sh")
PROOF_SBATCH_LOC = Path("./jobs/run-proofs.sh")

PROOF_MAP_LOC = Path("./proof_maps")


@dataclass
class ProofMap:
    proofs: list[tuple[FileInfo, int]]

    def __len__(self) -> int:
        return len(self.proofs)

    def get(self, idx: int) -> tuple[FileInfo, int]:
        return self.proofs[idx]

    def to_json(self):
        objs: list[dict[str, str | int]] = []
        for f_info, proof_idx in self.proofs:
            objs.append({"file_info": f_info.to_json(), "proof_idx": proof_idx})
        return {"map": objs}

    def save(self, path: Path):
        with path.open("w") as fout:
            fout.write(json.dumps(self.to_json(), indent=2))

    @classmethod
    def from_json(cls, json_data: Any) -> ProofMap:
        proofs: list[tuple[FileInfo, int]] = []
        for obj in json_data["map"]:
            proofs.append((FileInfo.from_json(obj["file_info"]), obj["proof_idx"]))
        return cls(proofs)

    @classmethod
    def load(cls, path: Path) -> ProofMap:
        with path.open("r") as fin:
            return cls.from_json(json.load(fin))

    @classmethod
    def create(
        cls,
        data_split: DataSplit,
        split: Split,
        data_loc: Path,
        sentence_db: SentenceDB,
    ) -> ProofMap:
        proofs: list[tuple[FileInfo, int]] = []
        for f in tqdm(data_split.get_file_list(split)):
            f_proofs = f.get_proofs(data_loc, sentence_db)
            for i, _ in enumerate(f_proofs):
                proofs.append((f, i))
        return cls(proofs)


def create_eval_proof_map(eval_conf: EvalConf) -> ProofMap:
    if eval_conf.split == Split.TRAIN:
        raise ValueError("Evaluation on training set not supported.")

    proof_map_loc = PROOF_MAP_LOC / split2str(eval_conf.split)
    if proof_map_loc.exists():
        print(f"Using proof map located at {proof_map_loc}")
        return ProofMap.load(proof_map_loc)

    print(f"Creating proof map.")
    data_split = DataSplit.load(eval_conf.data_split_loc)
    sentence_db = SentenceDB.load(eval_conf.sentence_db_loc)
    proof_map = ProofMap.create(
        data_split, eval_conf.split, eval_conf.data_loc, sentence_db
    )
    proof_map.save(proof_map_loc)
    return proof_map


# def wait_for_servers(num_servers: int):
#     session = requests.Session()
#     urls: list[str] = []
#     for num in range(start_server_num, next_server_num):
#         url = f"http://servers-{num}/"
#         path = Path(SERVER_LOC) / str(num)
#         session.mount(f"http://servers-{i}/", ServerAdapter(path))
#         urls.append(url)

#     assert len(open_processes) == len(urls)
#     for process, server_url in zip(started_processes, urls):
#         while True:
#             try:
#                 poll_result = subprocess.Popen.poll(process)
#                 if poll_result is not None:
#                     raise ServerFailedError
#                 response = session.get(server_url)
#                 break
#             except requests.exceptions.RequestException:
#                 continue

def wait_for_servers(
    next_server_num: int
):
    session = requests.Session()
    urls: list[str] = []
    for num in range(next_server_num):
        url = f"http://servers-{num}/"
        path = Path(SERVER_LOC) / str(num)
        session.mount(f"http://servers-{num}/", ServerAdapter(path))
        urls.append(url)

    for server_url in urls:
        while True:
            try:
                response = session.get(server_url)
                break
            except requests.exceptions.RequestException:
                continue



def run(
    eval_conf: EvalConf,
    timeout: str,
    n_tasks_per_node: int,
    n_gpu_nodes: int,
    n_cpu: int,
):
    server_commands: Optional[list[StartModelCommand]] = None
    clean_eval_confs: list[TopLevelConf] = []
    next_server_num = 0
    n_tasks = n_tasks_per_node * n_gpu_nodes
    for _ in range(n_tasks):
        clean_eval_conf, next_server_num, commands = to_client_conf(
            eval_conf, next_server_num
        )
        clean_eval_confs.append(clean_eval_conf)
        if server_commands is None:
            server_commands = commands
        else:
            assert len(server_commands) == len(commands)
    assert server_commands is not None

    final_eval_conf = merge(clean_eval_confs)
    with RUN_MODELS_LOC.open("w") as fout:
        commands = [
            " ".join(c.to_list_slurm("SLURM_PROC_ID", len(server_commands)))
            for c in server_commands
        ]
        run_model_file = "#!/bin/bash\n" + "source venv/bin/activate\n" + "\n".join(commands)
        fout.write(run_model_file)

    server_sbatch = (
        "#!/bin/bash\n"
        f"#SBATCH -p gpu-preempt\n"
        f"#SBATCH -t {timeout}\n"
        f"#SBATCH --ntasks={n_tasks_per_node * n_gpu_nodes}\n"
        f"#SBATCH --nodes={n_gpu_nodes}\n"
        f"#SBATCH --ntasks-per-node={n_tasks_per_node}\n"
        #f"#SBATCH --cpus-per-task=1\n"
        f"#SBATCH --gpus-per-task=1\n"
				f"#SBATCH -o slurm-serve-%j.out\n"
        f"srun -l {RUN_MODELS_LOC}\n"
    )

    with GPU_SBATCH_LOC.open("w") as fout:
        fout.write(server_sbatch)

    # Start gpus
    print("Starting gpu servers...")
    subprocess.run(["sbatch", f"{GPU_SBATCH_LOC}"])

    proof_map = create_eval_proof_map(eval_conf)
    eval_conf_loc = CLEAN_CONFIG + datetime.now().strftime("%m%d%H%M%S") 
    with open(eval_conf_loc, "wb") as fout:
        pickle.dump(final_eval_conf, fout)

    wait_for_servers(next_server_num)

    proof_map_loc = PROOF_MAP_LOC / split2str(eval_conf.split)
    proof_sbatch = (
        "#!/bin/bash\n"
        f"#SBATCH -p cpu-preempt\n"
        f"#SBATCH -c {n_cpu}\n"
        f"#SBATCH -t {timeout}\n"
        f"#SBATCH --array=0-{len(proof_map)}%{n_cpu}\n"
				f"SBATCH -o slurm-prove-%j.out\n"
        f"timout {2 * eval_conf.search_conf.timeout} python3 src/evaluation/eval_proof.py {eval_conf_loc} {proof_map_loc} $SLURM_ARRAY_TASK_ID\n"
    )

    with PROOF_SBATCH_LOC.open("w") as fout:
        fout.write(proof_sbatch)
    
		# Start proof workers
    print("Starting proof workers...")
    subprocess.run(["sbatch", f"{PROOF_SBATCH_LOC}"])



if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("conf_loc", help="Location of eval configuration")
    parser.add_argument("timeout", help="Timeout for evaluation")
    parser.add_argument("n_gpu_tasks_per_node", type=int, help="Number of gpus per node")
    parser.add_argument("n_gpu_nodes", type=int, help="Number of nodes.")
    parser.add_argument("n_cpus", type=int, help="Number of cpus to use")
    args = parser.parse_args(sys.argv[1:])

    conf_loc = Path(args.conf_loc)
    timeout = args.timeout
    n_gpu_tasks_per_node = args.n_gpu_tasks_per_node
    n_gpu_nodes = args.n_gpu_nodes
    n_cpus = args.n_cpus

    assert conf_loc.exists()
    assert isinstance(timeout, str)
    assert isinstance(n_gpu_tasks_per_node, int)
    assert isinstance(n_gpu_nodes, int)
    assert isinstance(n_cpus, int)

    with conf_loc.open("r") as fin:
        conf = yaml.load(fin, Loader=yaml.Loader)

    eval_conf = EvalConf.from_yaml(conf)
    run(eval_conf, timeout, n_gpu_tasks_per_node, n_gpu_nodes, n_cpus) 
