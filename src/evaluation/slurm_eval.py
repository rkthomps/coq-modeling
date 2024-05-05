from __future__ import annotations
import sys, os
import json
from typing import Any
from pathlib import Path
from dataclasses import dataclass
from tqdm import tqdm

import argparse
import yaml
from evaluation.evaluate import EvalConf
from data_management.splits import Split, split2str, DataSplit, FileInfo
from data_management.sentence_db import SentenceDB

from model_deployment.tactic_gen_client import FidTacticGenConf, CodellamaTacticGenConf

RUN_MODEL_LOC = Path("./slurm/run-model.sh")
TACTIC_SERVER_LOC = Path("./src/model_deployment/tactic_gen_server.py")
GPU_SBATCH_LOC = Path("./slurm/run-gpus.sh")

PROOF_MAP_LOC = Path("./proof_maps")


@dataclass
class ProofMap:
    proofs: list[tuple[FileInfo, int]] = []

    def get(self, idx: int) -> tuple[FileInfo, int]:
        return self.proofs[idx]

    def to_json(self):
        objs: list[dict[str, str | int]] = []
        for f_info, proof_idx in self.proofs:
            objs.append({
                "file_info": f_info.to_json(),
                "proof_idx": proof_idx
            })
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
    def create(cls, data_split: DataSplit, split: Split, data_loc: Path, sentence_db: SentenceDB) -> ProofMap:
        proofs: list[tuple[FileInfo, int]] = []
        for f in tqdm(data_split.get_file_list(split)):
            f_proofs = f.get_proofs(data_loc, sentence_db)
            for i, _ in enumerate(f_proofs):
                proofs.append((f, i))
        return cls(proofs)


def create_eval_proof_map(eval_conf: EvalConf) -> ProofMap:
    if eval_conf.split == Split.TRAIN:
        raise ValueError("Evaluation on training set not supported.")

    proof_map_loc = PROOF_MAP_LOC /  split2str(eval_conf.split)
    if proof_map_loc.exists():
        print(f"Using proof map located at {proof_map_loc}")
        return ProofMap.load(proof_map_loc)
    
    print(f"Creating proof map.")
    data_split = DataSplit.load(eval_conf.data_split_loc)
    sentence_db = SentenceDB.load(eval_conf.sentence_db_loc)
    proof_map = ProofMap.create(data_split, eval_conf.split, eval_conf.data_loc, sentence_db)
    proof_map.save(proof_map_loc)
    return proof_map 


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
