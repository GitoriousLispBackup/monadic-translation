Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.ClassicalChoice.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Wf_nat.
Require Import "Misc/Relation".

Module Injection.

  Definition injective_relation (R:relation nat) : Prop :=
    forall (m1 m2 n:nat), R m1 n -> R m2 n -> m1 = m2.

  Definition injective_function (f:nat -> nat) : Prop :=
    forall (m n:nat), m <> n -> f m <> f n.

  Definition not_in_image (R:relation nat) (x:nat) : Prop :=
    forall (m:nat), ~ R m x.

  Record t : Type := mkT {
    get : nat -> nat ;
    injective: injective_function get
  }.

  Definition disjoint_function (R:relation nat) (f:t) : Prop :=
    forall x, not_in_image R (get f x).

  Lemma id_injective:
    injective_function (fun x => x).
  Proof.
    unfold injective_function ; tauto.
  Qed.

  Lemma next_injective:
    forall (acc:t),
    injective_function (fun n => (get acc) (S n)).
  Proof.
    unfold injective_function ; intros ; simpl.
    apply (injective acc).
    omega.
  Qed.

  Lemma left_injective:
    forall (acc:t),
    injective_function (fun n => (get acc) (2*n)).
  Proof.
    unfold injective_function ; intros ; simpl.
    apply (injective acc).
    omega.
  Qed.

  Lemma right_injective:
    forall (acc:t),
    injective_function (fun n => (get acc) (2*n+1)).
  Proof.
    unfold injective_function ; intros ; simpl.
    apply (injective acc).
    omega.
  Qed.

  Definition id : t := mkT (fun n => n) id_injective.

  Definition succ (acc:t) : t := mkT 
    (fun n => (get acc) (S n)) (next_injective acc).

  Definition left (acc:t) : t := mkT 
    (fun n => (get acc) (2*n)) (left_injective acc).

  Definition right (acc:t) : t := mkT
    (fun n => (get acc) (2*n+1)) (right_injective acc).

  Definition split (acc:t) : t * t := (left acc, right acc).

  Definition completion (R:relation nat) (f:t) (x y:nat) : Prop :=
    R x y \/ (forall y, ~ R x y) /\ y = (get f x).

  Lemma completion_extension:
    forall (R:relation nat) (f:t) (m p:nat),
      R m p -> completion R f m p.
  Proof.
    intros ; left ; assumption.
  Qed.

  Lemma completion_partial_function:
    forall (R:relation nat) (f:t),
      partial_function R ->
      partial_function (completion R f).
  Proof.
    intros ; unfold partial_function ; intros.
    unfold completion in *|-*.
    destruct H0 ; destruct H1.
    specialize (H x y1 y2 H0 H1) ; assumption.
    destruct H1.
    apply H1 in H0 ; contradiction.
    destruct H0.
    apply H0 in H1 ; contradiction.
    destruct H0 ; destruct H1 ; subst ; reflexivity.
  Qed.

  Lemma completion_total:
    forall (R:relation nat) (f:t) (x:nat),
      exists y, (completion R f) x y.
  Proof.
    intros.
    assert((forall y, ~ R x y) \/ ~(forall y, ~ R x y)).
    apply classic.
    destruct H.
    exists (get f x).
    right ; split ; auto.
    apply not_all_not_ex in H.
    destruct H ; exists x0 ; left ; assumption.
  Qed.

  Lemma completion_function:
    forall (R:relation nat) (f:t),
      partial_function R ->
      function (completion R f).
  Proof.
    intros ; split ; intros.
    apply completion_partial_function ; assumption.
    apply completion_total ; assumption.
  Qed.


  Lemma completion_injective:
    forall (R:relation nat) (f:t),
      injective_relation R ->
      (forall x, not_in_image R (get f x)) ->
      injective_relation (completion R f).
  Proof.
    intros ; unfold completion.
    unfold injective_relation ; intros.
    destruct H1 ; destruct H2.
    specialize (H m1 m2 n H1 H2).
    assumption.
    destruct H2 ; subst.
    unfold not_in_image in H0.
    apply H0 in H1 ; contradiction.
    destruct H1 ; subst.
    apply H0 in H2 ; contradiction.
    destruct H1 ; destruct H2.
    subst.
    specialize (injective f m1 m2) ; intros.
    omega.
  Qed.

  Lemma completion_valid:
    forall (R:relation nat) (f:t),
      injective_relation R -> 
      partial_function R ->
      disjoint_function R f ->
      injective_relation (completion R f) /\ 
      function (completion R f) /\
      (forall (m n:nat), R m n -> (completion R f) m n).
   Proof.
     intros ; split ; [|split] ; intros.
     apply completion_injective ; assumption.
     apply completion_function ; assumption.
     apply completion_extension ; assumption.
   Qed.

  Lemma completion_exists:
    forall (R:relation nat) (f:t),
      injective_relation R -> 
      partial_function R ->
      disjoint_function R f ->
      exists g, forall (m n:nat), R m n -> (get g m) = n.
  Proof.
     intros.
     specialize (completion_valid R f H H0 H1) ; intros.
     destruct H2 ; destruct H3 ; destruct H3.
     specialize(choice (completion R f) H5) ; intros.
     destruct H6.
     assert(injective_function x).
     unfold injective_function ; intros.
     assert(H8 := H6 m).
     assert(H9 := H6 n).
     unfold not ; intros.
     rewrite H10 in H8.
     specialize (H2 m n (x n) H8 H9).
     subst ; omega.
     exists (mkT x H7).
     intros.
     simpl.
     apply H4 in H8.
     specialize (H6 m).
     specialize (H3 m n (x m) H8 H6).
     auto.
   Qed.

End Injection.
