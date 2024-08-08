from data_management.dataset_file import Proof, DatasetFile
from model_deployment.proof_manager import ProofManager


def build_dset_file(proof_manager: ProofManager, new_proof: Proof) -> DatasetFile:
    return DatasetFile()
