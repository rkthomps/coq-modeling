import time
from dataclasses import dataclass

from tactic_gen.lm_example import LmExample, ProofRetrievalFormatter, GPTProofFormatter
from data_management.dataset_file import DatasetFile

from model_deployment.tactic_gen_client import TacticGenClient
from model_deployment.proof_manager import ProofManager
from model_deployment.proof_manager import TacticResult


@dataclass
class WholeProofResult:
    prompt_example: LmExample
    successes: list[str]
    failures: list[str]
    time: float


class WholeProofSearcher:
    def __init__(
        self,
        tactic_gen_client: TacticGenClient,
        proof_manager: ProofManager,
        n_attempts: int,
    ):
        self.tactic_gen_client = tactic_gen_client
        self.proof_manager = proof_manager
        self.n_attempts = n_attempts
        assert len(self.tactic_gen_client.formatters) == 1
        self.formatter = self.tactic_gen_client.formatters[0]

    @property
    def need_goal_record(self) -> bool:
        return isinstance(self.formatter, ProofRetrievalFormatter | GPTProofFormatter)

    def search(self) -> WholeProofResult:
        initial_proof = ""
        initial_dset_file = self.proof_manager.get_initial_context()
        if initial_dset_file is None:
            raise ValueError("Could not get initial datasetfile")
        initial_proof_obj = initial_dset_file.proofs[-1]
        initial_check_result = self.proof_manager.check_proof(
            initial_proof, initial_proof_obj.theorem, self.need_goal_record
        )
        assert initial_check_result.tactic_result == TacticResult.VALID
        assert initial_check_result.current_goals is not None
        assert initial_check_result.new_proof is not None
        print(initial_check_result)

        start = time.time()
        example = self.proof_manager.get_example(
            self.formatter, initial_dset_file, initial_check_result.goal_record
        )
        model_result = self.tactic_gen_client.get_recs(
            example, self.n_attempts, initial_proof
        )

        successes: list[str] = []
        failures: list[str] = []
        for proof in model_result.next_tactic_list:
            added_newline_proof = f"\n{proof}"
            check_result = self.proof_manager.check_proof(
                added_newline_proof, initial_proof_obj.theorem, False
            )
            print(check_result)
            match check_result.tactic_result:
                case TacticResult.COMPLETE:
                    successes.append(added_newline_proof)
                case _:
                    failures.append(added_newline_proof)
        end = time.time()
        return WholeProofResult(example, successes, failures, end - start)
