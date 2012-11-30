Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Max.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

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

Lemma plus_minus:
  forall (m n p:nat), n <= p -> m+p-n = m+(p-n).
Proof.
  induction m ; intros.
  omega.
  omega.
Qed.

Lemma plus_minus_n:
  forall (m n:nat), m+n-n = m.
Proof.
  induction m ; intros.
  omega.
  omega.
Qed.

Module List2.

  Definition hd_cons {T:Type} (l:list T) (e:T) : T * list T :=
    match l with
    | nil => (e, nil)
    | e :: l => (e, l)
    end.

  Fixpoint map_iter {T T':Type} (f:T -> nat -> T') (l:list T) (n:nat) :=
    match l with
    | nil => nil
    | cons e l => (f e n) :: map_iter f l (S n)
    end.

End List2.

Module List2Properties.

  Import List2.

  Lemma length_map_iter:
    forall {T T':Type} (f:T -> nat -> T') (l:list T) (n:nat),
    length (map_iter f l n) = length l.
  Proof.
    induction l ; simpl ; intros ; auto.
  Qed. 

  Lemma map_iter_app:
    forall {T T':Type} (f:T -> nat -> T') (l1 l2:list T) (n:nat),
    map_iter f (l1++l2) n = (map_iter f l1 n)++(map_iter f l2 (n+(length l1))).
  Proof.
    induction l1 ; simpl ; intros ; auto.
    rewrite IHl1.
    rewrite plus_Snm_nSm.
    reflexivity.
  Qed. 

  Lemma map_iter_nth:
    forall {T T':Type} (f:T -> nat -> T') (l:list T) (m n:nat) (e:T),
    nth m (map_iter f l n) (f e (m+n)%nat) = f (nth m l e) (m+n)%nat.
  Proof.
    induction l ; simpl ; intros.
    destruct n ; destruct m ; reflexivity.
    destruct m.
    reflexivity.
    simpl.
    specialize (IHl m (S n)).
    rewrite <- plus_Snm_nSm in IHl.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma map_iter_nth_indep:
    forall {T T':Type} (f:T -> nat -> T') (l:list T) (m n:nat) (e1:T) (e2:T'),
    m < length l ->
    nth m (map_iter f l n) e2 = f (nth m l e1) (m+n)%nat.
  Proof.
    intros.
    rewrite nth_indep with (d':=f e1 (m+n)%nat).
    apply map_iter_nth.
    rewrite length_map_iter.
    assumption.
  Qed.

End List2Properties.