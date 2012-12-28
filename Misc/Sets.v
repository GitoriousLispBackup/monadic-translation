Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Arith.NatOrderedType.
Require Import Coq.MSets.MSetList.
Require Import Coq.MSets.MSetProperties.
Require Import Coq.MSets.MSetEqProperties.
Require Import "Misc/Tactics".


(** * Nat Set *)
Module Nat_as_OWL <: OrderedTypeWithLeibniz.
  Include Nat_as_OT.
  Lemma eq_leibniz : forall x y, eq x y -> x = y.
  Proof.
    intros ; assumption.
  Qed.
End Nat_as_OWL.

(** ** Definitions *)
Module NatSet.

  (** MSet is used internally *)
  Module MSetIntern := MSetList.MakeWithLeibniz Nat_as_OWL.

  (** Public methods are inherited from MSet *)
  Import MSetIntern.

  Definition t := t.
  Definition empty := empty.
  Definition singleton := singleton.
  Definition add := add.
  Definition mem := mem.
  Definition remove := remove.

End NatSet.

(** ** Properties *)
Module NatSetProperties.

  Import NatSet.
  Module MSetProps := WPropertiesOn Nat_as_OT MSetIntern.
  Module MSetEqProps := WEqPropertiesOn Nat_as_OT MSetIntern.
  Import MSetIntern.

  Lemma add_mem_1:
    forall (lst:t) (n:nat), 
    mem n lst = true -> add n lst = lst.
  Proof.
    intros.
    apply eq_leibniz, MSetProps.add_equal, mem_spec.
    assumption.
  Qed.

  Lemma add_mem_2:
    forall (lst:t) (n m:nat), 
    mem n lst = true -> mem n (add m lst) = true.
  Proof.
    intros ; apply MSetEqProps.add_mem_3 ; assumption.
  Qed.

  Lemma add_mem_3:
    forall (lst:t) (n:nat), 
    mem n (add n lst) = true.
  Proof.
    intros ; apply MSetEqProps.add_mem_1 ; assumption.
  Qed.

  Lemma add_mem_4:
    forall (lst:t) (n m:nat),
    m <> n -> mem n (add m lst) = mem n lst.
  Proof.
    intros ; apply MSetEqProps.add_mem_2 ; assumption.
  Qed.

  Lemma add_mem_5:
    forall (lst:t) (n m:nat),
    mem n (add m lst) = false -> mem n lst = false.
  Proof.
    intros ; case_beq_nat m n.
    rewrite add_mem_3 in H ; inversion H.
    rewrite add_mem_4 in H ; assumption.
  Qed.

  Lemma add_mem_6:
    forall (lst:t) (n m:nat),
    mem n (add m lst) = false -> m <> n.
  Proof.
    intros ; case_beq_nat m n.
    rewrite add_mem_3 in H ; inversion H.
    rewrite add_mem_4 in H ; assumption.
  Qed.

  Lemma add_add:
    forall (lst:t) (m n:nat),
    add m (add n lst) = add n (add m lst).
  Proof.
    intros ; apply eq_leibniz, MSetProps.add_add.
  Qed.

  Lemma remove_mem_1:
    forall (lst:t) (n m:nat),
    m <> n -> mem n (remove m lst) = mem n lst.
  Proof.
    intros ; apply MSetEqProps.remove_mem_2 ; assumption.
  Qed.

  Lemma remove_mem_2:
    forall (lst:t) (n:nat),
    mem n (remove n lst) = false.
  Proof.
    intros ; apply MSetEqProps.remove_mem_1 ; assumption.
  Qed.

  Lemma remove_mem_3:
    forall (lst:t) (n m:nat),
    mem n lst = false ->
    mem n (remove m lst) = false.
  Proof.
    intros ; case_beq_nat m n.
    apply remove_mem_2.
    rewrite remove_mem_1 ; assumption.
  Qed.

  Lemma remove_equal:
    forall (lst:t) (n:nat),
    mem n lst = false ->
    remove n lst = lst.
  Proof.
    intros ; apply eq_leibniz, MSetProps.remove_equal.
    red ; intros.
    apply mem_spec in H0.
    rewrite H in H0 ; inversion H0.
  Qed.

  Lemma remove_empty:
    forall (n:nat), remove n empty = empty.
  Proof.
    intros ; apply eq_leibniz, MSetProps.remove_equal.
    red ; intros.
    inversion H.
  Qed.

  Lemma singleton_equal_add:
    forall (n:nat),
    singleton n = add n empty.
  Proof.
    intros ; apply eq_leibniz, MSetProps.singleton_equal_add ; 
    assumption.
  Qed.

  Lemma equal_mem_1:
    forall (l1 l2:t),
    (forall (m:nat), mem m l1 = mem m l2) -> l1 = l2.
  Proof.
    intros.
    apply eq_leibniz, equal_spec.
    rewrite MSetEqProps.equal_mem_1 ; trivial.
  Qed.

  Lemma empty_union_1:
     forall (l:t),
     union empty l = l.
  Proof.
    intros.
    apply eq_leibniz, MSetProps.empty_union_1.
    apply empty_spec.
  Qed.

  Lemma union_add:
     forall (l1 l2:t) (n:nat),
     union (add n l1) l2 = add n (union l1 l2).
  Proof.
    intros.
    apply eq_leibniz, MSetProps.union_add.
  Qed.

  Lemma singleton_union_1:
    forall (l:t) (n:nat),
    union (singleton n) l = add n l.
  Proof.
    intros ; symmetry.
    apply eq_leibniz, equal_spec.
    apply MSetEqProps.add_union_singleton.
  Qed.

End NatSetProperties.
