





from data_management.dataset_file import DatasetFile
from coqpyt.coq.proof_file import ProofFile


class DataPointsCache:
    def __init__(self, cache_loc: str):
        self.cache_loc = cache_loc