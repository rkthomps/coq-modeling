import numpy as np

from data_management.dataset_file import DatasetFile, FocusedStep, Proof, Sentence
from model_deployment.premise_model_wrapper import LocalPremiseModelWrapper
from premise_selection.premise_example import PremiseTrainingExample


def premise_training_examples_from_step(
    step: FocusedStep,
    proof: Proof,
    dataset_file: DatasetFile,
    num_negatives: int,
    base_model: LocalPremiseModelWrapper,
    beta: float = 0.5,
) -> list[PremiseTrainingExample]:
    filter_result = base_model.premise_filter.get_pos_and_avail_premises(
        step, proof, dataset_file
    )
    formatted_pos_prems = [
        base_model.premise_format.format(p) for p in filter_result.pos_premises
    ]
    negatives: list[Sentence] = []
    for premise in filter_result.avail_premises:
        formatted_prem = base_model.premise_format.format(premise)
        if formatted_prem in formatted_pos_prems:
            continue
        negatives.append(premise)

    formatted_context = base_model.context_format.format(step, proof)
    negative_scores = base_model.get_premise_scores_from_strings(
        formatted_context, negatives
    )
    negative_np_scores = np.array(negative_scores)
    negative_np_exps = np.exp(negative_np_scores * beta)
    negative_np_dist = negative_np_exps / negative_np_exps.sum()

    training_examples: list[PremiseTrainingExample] = []
    for pos_prem in formatted_pos_prems:
        if num_negatives < len(negatives):
            example_negatives = negatives
        else:
            example_negatives = np.random.choice(
                negatives, num_negatives, p=negative_np_dist
            )
        formatted_negatives = [
            base_model.premise_format.format(n) for n in example_negatives
        ]
        training_examples.append(
            PremiseTrainingExample(
                formatted_context,
                pos_prem,
                formatted_negatives,
                formatted_pos_prems,
            )
        )
    return training_examples
