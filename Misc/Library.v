Require Import Coq.Arith.Arith.

Lemma beq_nat_sym : forall n1 n2, beq_nat n1 n2 = beq_nat n2 n1.
Proof.
  induction n1; destruct n2; simpl; auto.
Qed.