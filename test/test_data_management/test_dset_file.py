

from data_management.dataset_file import DatasetFile, Proof, Term, FocusedStep
from coqpyt.coq.structs import TermType


class TestDsetFile:
    """Really I should have a test coq file, and assert properties about it."""

    THM1 = "Theorem prestrict_length p s : length (prestrict p s) = (length s)."
    THM2 = "Definition cross1 := let p := indexes in let q := ref_list in fold_right (fun x l => (map (fun y => (x, y)) q) ++ l) nil p."
    TERM1 = Term.from_text(THM1, TermType.THEOREM)
    TERM2 = Term.from_text(THM2, TermType.DEFINITION)
    INTRO_STEP = FocusedStep.from_step_text(" intros.") 
    DEF_STEP = FocusedStep.from_step_text(" Defined.")
    QED_STEP = FocusedStep.from_step_text(" Qed.")
    PROOF1 = Proof(TERM1, [INTRO_STEP, DEF_STEP])
    PROOF2 = Proof(TERM1, [INTRO_STEP, QED_STEP])
    PROOF3 = Proof(TERM2, [INTRO_STEP, DEF_STEP])

    def test_proof_independent(self):
        assert not self.PROOF1.is_proof_independent()
        assert self.PROOF2.is_proof_independent()
        assert self.PROOF1.get_theorem_name() == "prestrict_length" 
        assert self.PROOF3.get_theorem_name() == "cross1" 

    def test_theorem_name(self):
        pass

    @classmethod
    def setup_class(cls) -> None:
        pass

    @classmethod
    def teardown_class(cls) -> None:
        pass
