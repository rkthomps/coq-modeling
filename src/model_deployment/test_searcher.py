

from data_management.lm_example import LmExample, BasicLmExample
from model_deployment.model_wrapper import ModelResult, ModelWrapper, CodeLLamaNodeScore
from model_deployment.searcher import SearchTreeManager
from model_deployment.searcher import ProofManager 


class TestModelWrapper(ModelWrapper):
    def __init__(self) -> None:
        pass

    def get_recs(self, example: LmExample, n: int) -> ModelResult:
        tactics = [
            "intros.",
            " induction n as [|n' IHn'].",
            "\n-",
            "  reflexivity.",
            "\n-", 
            " simpl. apply IHn'.",
        ]

        scores = [
            CodeLLamaNodeScore(-0.1, 5),
            CodeLLamaNodeScore(-0.1, 5),
            CodeLLamaNodeScore(-0.1, 5),
            CodeLLamaNodeScore(-0.1, 10),
            CodeLLamaNodeScore(-0.1, 5),
            CodeLLamaNodeScore(-0.1, 8),
        ]
        return ModelResult(tactics, scores)


if __name__ == "__main__":
    file_path = "/home/ubuntu/coq-modeling/test-coq-projs/harder_example.v"
    proof_manager = ProofManager(file_path, BasicLmExample)
    node_score_type = CodeLLamaNodeScore
    tree_manager = SearchTreeManager(
        TestModelWrapper(), proof_manager, node_score_type,
        3, 10
    )
    result = tree_manager.search()
    proof_manager.close()
    print(result.get_proof())