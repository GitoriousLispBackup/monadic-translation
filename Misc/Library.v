Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Max.
Require Import Coq.omega.Omega.

Lemma beq_nat_sym : 
  forall n1 n2, beq_nat n1 n2 = beq_nat n2 n1.
Proof.
  induction n1; destruct n2; simpl; auto.
Qed.

Lemma max_0 : 
  forall n1 n2, max n1 n2 = 0 -> n1 = 0 /\ n2 = 0.
Proof.
  intros ; induction n1.
  auto.
  simpl in *|-*.
  destruct n2.
  inversion H.
  inversion H.
Qed.
