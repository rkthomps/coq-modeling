import sys, os
import ipdb

from coqpyt.coq.base_file import CoqFile

from model_deployment.mine_goal_terms import mine_coq_file_goals
from data_management.splits import FileInfo, Split
from util.util import get_fresh_path

test1 = """\
Lemma add_0_r: forall n1 : nat, n1 + 0 = n1.
Proof. 
  intros n1. 
  induction n1 as [|n1 IHn1].
  - reflexivity.
  - simpl. rewrite IHn1. reflexivity.
Qed.
"""

test2 = """\
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Fixpoint min (l : (list nat)) : option nat := 
    match l with
    | nil => None
    | h :: tl => match (min tl) with
        | None => Some h 
        | Some m => if (h <? m) then (Some h) else (Some m)
        end
    end.

Lemma exists_min: forall (l : (list nat)), 
    (l <> nil) -> exists h, min(l) = Some(h).
Proof.
  intros. destruct l.  
  - contradiction. 
  - simpl. destruct (min l).
    + destruct (n <? n0).
      * exists n. reflexivity.       
      * exists n0. reflexivity.
    + exists n. reflexivity.
Qed.
"""

test3 = """\
Require Import ZArith.
Require Import Setoid.

Local Open Scope Z_scope.

Add Parametric Relation : Z Z.le
reflexivity proved by Z.le_refl
transitivity proved by Z.le_trans as le.

Lemma eq_Zle : forall (x y : Z), x = y -> x <= y.
Proof.
intros ; subst ; reflexivity.
Qed.
"""


class TestMineFileGoals:
    def __mock_file_info(self, filename: str) -> FileInfo:
        return FileInfo(os.path.basename(filename), filename, ".", ".")

    def test_mine_goals1(self) -> None:
        test_file_info = self.__mock_file_info(self.file1_path)
        with CoqFile(self.file1_path) as coq_file:
            records = mine_coq_file_goals(coq_file, test_file_info, Split.TRAIN)
            assert len(records) == 6

    def test_mine_goals2(self) -> None:
        test_file_info = self.__mock_file_info(self.file2_path)
        with CoqFile(self.file2_path) as coq_file:
            records = mine_coq_file_goals(coq_file, test_file_info, Split.TRAIN)
            assert len(records) == 12

    # Leads to a weird match branch that seemingly doesn't get rid of all notations
    # def test_mine_goals3(self) -> None:
    #     test_file_info = self.__mock_file_info(self.file3_path)
    #     with CoqFile(self.file3_path) as coq_file:
    #         records = mine_coq_file_goals(coq_file, test_file_info, Split.TRAIN)
    #         assert len(records) == 12

    @classmethod
    def setup_class(cls) -> None:
        cls.file1_path = get_fresh_path(".", "file1.v")
        with open(cls.file1_path, "w") as fout:
            fout.write(test1)

        cls.file2_path = get_fresh_path(".", "file2.v")
        with open(cls.file2_path, "w") as fout:
            fout.write(test2)

        cls.file3_path = get_fresh_path(".", "file3.v")
        with open(cls.file3_path, "w") as fout:
            fout.write(test3)

    @classmethod
    def teardown_class(cls) -> None:
        if os.path.exists(cls.file1_path):
            os.remove(cls.file1_path)
        if os.path.exists(cls.file2_path):
            os.remove(cls.file2_path)
        if os.path.exists(cls.file3_path):
            os.remove(cls.file3_path)
