import ipdb
from data_management.dataset_file import FocusedStep, Proof, Term, Sentence, Goal
from model_deployment.premise_model_wrapper import (
    LocalRerankModelWrapper,
    LocalPremiseModelWrapper,
    get_ranked_premise_generator,
    TFIdf,
    BM25Okapi,
)

from coqpyt.coq.structs import TermType


# pmw = TFIdf()
# pmw = BM25Okapi()
# pmw = LocalRerankModelWrapper.from_checkpoint(
#     "/home/kthompson/coq-modeling/models/rerank-15-pos-opt/checkpoint-500"
# )
# pmw = LocalRerankModelWrapper.from_checkpoint(
#     "/home/kthompson/coq-modeling/models/rerank-15-pos-all/checkpoint-500"
# )
# pmw = LocalRerankModelWrapper.from_checkpoint(
#     "/home/kthompson/coq-modeling/models/rerank-15-all/checkpoint-11500"
# )
pmw = LocalPremiseModelWrapper.from_checkpoint(
    "/home/kthompson/coq-modeling/models/prem-select-opt/checkpoint-2200"
)


thm_statement = "Theorem add_comm: forall (n m : nat), n + m = m + n."
step_0_goals = [Goal([], "forall (n m: nat), n + m = m + n")]
step_0_text = "\n  intros."
step_0 = FocusedStep.from_step_and_goals(thm_statement, step_0_text, step_0_goals)


step_1_goals = [Goal(["n m : nat"], "n + m = m + n")]
step_1_text = " induction n."
step_1 = FocusedStep.from_step_and_goals(thm_statement, step_1_text, step_1_goals)

step_2_goals = [
    Goal(["m : nat"], "0 + m = m + 0"),
    Goal(["n m : nat", "IHn : n + m = m + n"], "S n + m = m + S n"),
]
step_2_text = "\n  -"
step_2 = FocusedStep.from_step_and_goals(thm_statement, step_2_text, step_2_goals)

step_3_goals = [
    Goal(["m : nat"], "0 + m = m + 0"),
]
step_3_text = "  Admitted."
step_3 = FocusedStep.from_step_and_goals(thm_statement, step_3_text, step_3_goals)


current_proof = Proof(
    Term.from_text(thm_statement, TermType.THEOREM), [step_0, step_1, step_2, step_3]
)
premise_1 = Sentence.from_text(
    "Lemma add_0_r: forall (n : nat), n + 0 = n.", TermType.LEMMA
)
premise_2 = Sentence.from_text(
    "Lemma app_assoc: forall {A : Type} (l1 l2 l3: list A), l1 ++ l2 ++ l3 = l1 ++ (l2 ++ l3).",
    TermType.LEMMA,
)

premise_3 = Sentence.from_text(
    "Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).",
    TermType.THEOREM,
)

# premises, probs = pmw.rerank(step_3, current_proof, [premise_1, premise_2, premise_3])
# for premise, prob in zip(premises, probs):
#     print(premise.text, prob)

# ipdb.set_trace()


# Some models only retr
premise_generator = get_ranked_premise_generator(
    pmw, step_1, current_proof, [premise_1, premise_2, premise_3]
)

for i, premise in enumerate(premise_generator):
    print(f"Premise {i + 1}: {premise.text}")

# To see the scores:
formatted_ctxt = pmw.context_format.format(step_1, current_proof)
formatted_premises = [
    pmw.premise_format.format(p) for p in [premise_1, premise_2, premise_3]
]
print(pmw.get_premise_scores_from_strings(formatted_ctxt, formatted_premises))
