
from data_management.dataset_file import Proof, FocusedStep, Sentence

class ContextFormat:
    @staticmethod
    def format(step: FocusedStep, proof: Proof) -> str:
        raise NotImplementedError

    @staticmethod
    def get_alias() -> str:
        raise NotImplementedError


class BasicContextFormat(ContextFormat):
    @staticmethod
    def format(step: FocusedStep, proof: Proof) -> str:
        partial_proof = proof.proof_prefix_to_string(step)
        goal_strs: list[str] = []
        for i, goal in enumerate(step.goals):
            goal_strs.append(f"Goal {i + 1}:\n{goal.to_string()}")
        goal_str = "\n\n".join(goal_strs)
        return f"{partial_proof}\n\n{goal_str}"

    @staticmethod
    def get_alias() -> str:
        return "basic-context-format"


CONTEXT_ALIASES: dict[str, type[ContextFormat]] = {
    BasicContextFormat.get_alias(): BasicContextFormat,
}


class PremiseFormat:
    @staticmethod
    def format(sentence: Sentence) -> str:
        raise NotImplementedError

    @staticmethod
    def get_alias() -> str:
        raise NotImplementedError


class BasicPremiseFormat(PremiseFormat):
    @staticmethod
    def format(sentence: Sentence) -> str:
        return sentence.text

    @staticmethod
    def get_alias() -> str:
        return "basic-premise-format"


PREMISE_ALIASES: dict[str, type[PremiseFormat]] = {
    BasicPremiseFormat.get_alias(): BasicPremiseFormat,
}


