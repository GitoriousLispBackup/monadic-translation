Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.Classical.
Require Import Coq.Classes.Morphisms.
Require Import "Misc/Sets".
Require Import Coq.omega.Omega.
Require Import "Misc/Tactics".

(** * Replacement *)

Module Type Replacement.

  Parameter rho : nat -> bool.
  Parameter rho_O : rho 0 = true.

End Replacement.

(** * Stage Set *)

(** ** Definitions *)
Module StageSet.

  Include NatSet.
  Import MSetIntern.

  Definition ub (n:nat) (S:t) : bool :=
    for_all (fun x => leb x n) S.

End StageSet.

(** ** Properties *)
Module StageSetProperties.

  Import StageSet.
  Import MSetIntern.
  Export NatSet.

  Include NatSetProperties.
 
  Lemma ub_empty:
    forall (n:nat),
    ub n empty = true.
  Proof.
    intros.
    assert(forall n, Proper (Logic.eq ==> Logic.eq) 
      (fun x : elt => leb x n)).
    intros x s1 s2 H1 ; subst ; reflexivity.
    apply MSetEqProps.for_all_mem_1 ; auto ; intros.
    rewrite MSetEqProps.empty_mem in H0.
    inversion H0.
  Qed.

  Lemma ub_mem_1:
    forall (lst:t) (n m:nat),
    m < n -> ub m lst = true -> mem n lst = false.
  Proof.
    intros.
    assert(forall n, Proper (Logic.eq ==> Logic.eq) 
      (fun x : elt => leb x n)).
    intros x s1 s2 H1 ; subst ; reflexivity.
    remember (mem n lst) ; destruct b ; symmetry in Heqb ; auto ; exfalso.
    apply MSetEqProps.for_all_mem_2 with (x:=n) in H0 ; auto.
    apply leb_iff in H0 ; omega.
  Qed.

  Lemma ub_remove_equal:
    forall (lst:t) (n m:nat),
    m < n -> ub m lst = true -> remove n lst = lst.
  Proof.
    intros.
    apply remove_equal.
    apply ub_mem_1 with (m:=m) ; auto.
  Qed.

  Lemma ub_le_1:
    forall (lst:t) (n m:nat),
    m <= n -> ub n lst = ub n (add m lst).
  Proof.
    intros.
    assert(Proper (Logic.eq ==> Logic.eq) (fun x : elt => leb x n)).
    intros s1 s2 H1 ; subst ; reflexivity.
    assert(ub n lst = true \/ ~ub n lst = true).
    apply classic.
    destruct H1.
    rewrite H1 ; symmetry.
    apply MSetEqProps.for_all_mem_1.
    assumption.
    intros.
    case_beq_nat m x.
    apply leb_iff ; assumption.
    rewrite MSetEqProps.add_mem_2 in H2.
    apply MSetEqProps.for_all_mem_2 with (x:=x) in H1 ; assumption.
    assumption.
    apply not_true_is_false in H1 ; rewrite H1 ; symmetry.
    apply MSetEqProps.for_all_mem_4 in H1.
    destruct H1 ; destruct a.
    apply MSetEqProps.for_all_mem_3 with (x:=x).
    assumption.
    apply MSetEqProps.add_mem_3 ; assumption.
    assumption.
    assumption.
  Qed.

  Lemma ub_le_2:
    forall (lst:t) (n m:nat),
    m <= n -> ub m lst = true -> ub n lst = true.
  Proof.
    intros.
    assert(forall n, Proper (Logic.eq ==> Logic.eq) 
      (fun x : elt => leb x n)).
    intros x s1 s2 H1 ; subst ; reflexivity.
    apply MSetEqProps.for_all_mem_1 ; intros.
    apply H1.
    apply MSetEqProps.for_all_mem_2 with (x:=x) in H0.
    apply leb_iff in H0 ; apply leb_iff.
    omega.
    apply H1.
    assumption.
  Qed.

  Lemma ub_le_3:
    forall (lst:t) (n m:nat),
    ub n lst = true -> mem m lst = true -> m <= n.
  Proof.
    intros ; unfold ub in H.
    apply MSetEqProps.for_all_mem_2 with (x:=m) in H.
    apply leb_iff in H ; assumption.
    intros x ; intros ; subst ; reflexivity.
    assumption.
  Qed.

  Lemma ub_pred:
    forall (lst:t) (n:nat),
    ub n lst = ub (pred n) (remove n lst).
  Proof.
    assert(forall n, Proper (Logic.eq ==> Logic.eq) 
      (fun x : elt => leb x n)).
    intros x s1 s2 H1 ; subst ; reflexivity.
    intros.
    assert(ub n lst = true \/ ~ub n lst = true).
    apply classic.
    destruct H0 ; [| apply not_true_is_false in H0] ;
    rewrite H0 ; symmetry.
    apply MSetEqProps.for_all_mem_1 ; intros.
    apply H.
    apply MSetEqProps.for_all_mem_2 with (x:=x) in H0.
    apply leb_iff in H0 ; apply leb_iff.
    case_beq_nat x n.
    rewrite MSetEqProps.remove_mem_1 in H1 ; inversion H1.
    omega.
    apply H.
    apply MSetEqProps.remove_mem_3 in H1 ; assumption. 
    apply MSetEqProps.for_all_mem_4 in H0.
    destruct H0 ; destruct a.
    apply MSetEqProps.for_all_mem_3 with (x:=x).
    apply H.
    rewrite MSetEqProps.remove_mem_2.
    assumption.
    apply leb_iff_conv in H1 ; omega.
    apply leb_iff_conv in H1 ; apply leb_iff_conv ; omega.
    apply H.
  Qed.

  Lemma ub_S:
    forall (lst:t) (n:nat),
    ub (S n) lst = ub n (remove (S n) lst).
  Proof.
    intros ; apply ub_pred.
  Qed.

  Lemma add_ub:
   forall (lst:t) (n m:nat), ub n (add m lst) = true ->
   ub n lst = true.
  Proof.
    assert(forall n, Proper (Logic.eq ==> Logic.eq) 
      (fun x : elt => leb x n)).
    intros x s1 s2 H1 ; subst ; reflexivity.
    intros.
    unfold ub in H.
    apply MSetEqProps.for_all_mem_1 ; intros.
    apply H.
    apply MSetEqProps.for_all_mem_2 with (x:=x) in H0 ; trivial.
    apply add_mem_2 ; assumption.
  Qed.

  Lemma remove_add_remove:
    forall (lst:t) (n:nat),
    remove n (add n lst) = remove n lst.
  Proof.
    intros.
    remember(mem n lst).
    destruct b ; symmetry in Heqb.
    rewrite add_mem_1 ; auto.
    rewrite remove_equal with (lst:=lst) ; auto.
    apply MSetEqProps.remove_add in Heqb.
    apply eq_leibniz.
    apply equal_spec.
    assumption.
  Qed.

  Lemma remove_add_remove_2:
    forall (lst:t) (m n:nat),
    m <> n -> remove n (add m lst) = add m (remove n lst).
  Proof.
    intros.
    apply equal_mem_1 ; intros.
    case_beq_nat m0 m.
    rewrite MSetEqProps.add_mem_1.
    rewrite remove_mem_1.
    apply MSetEqProps.add_mem_1.
    auto.
    rewrite MSetEqProps.add_mem_2 ; auto.
    case_beq_nat m0 n.
    rewrite MSetEqProps.remove_mem_1 ; symmetry.
    apply MSetEqProps.remove_mem_1.
    rewrite MSetEqProps.remove_mem_2 ; auto.
    rewrite MSetEqProps.remove_mem_2 ; auto.
    rewrite MSetEqProps.add_mem_2 ; auto.
  Qed.

End StageSetProperties.

(** * Variable Set *)

(** ** Definitions *)
Module VarSet.

  Include NatSet.
  Import MSetIntern.

  Definition var := nat.

  Definition union := union.

End VarSet.

(** ** Properties *)
Module VarSetProperties.

  Import VarSet.
  Include NatSetProperties.

  Lemma union_mem:
    forall (s1 s2:t) (x:var),
    mem x (union s1 s2) = mem x s1 || mem x s2.
  Proof.
    intros ; apply MSetEqProps.union_mem.
  Qed.

  Lemma singleton_mem:
    forall (x y:var),
    mem x (singleton y) = true <-> y = x.
  Proof.
    intros.
    split ; intros.
    apply MSetEqProps.singleton_mem_3 in H.
    assumption.
    subst.
    apply MSetEqProps.singleton_mem_1.
  Qed.

End VarSetProperties.

(** * Binding Set *)

(** ** Definitions *)
Module BindingSet(Repl:Replacement).

  Definition t : Type := list StageSet.t.
  Definition var := nat.
  Definition stage := nat.

  Definition empty : t := nil.

  Fixpoint add (x:var) (n:stage) (B:t) : t :=
    match B, x with
    | nil, _ => (fix add x := 
      match x with
       | 0 => (StageSet.singleton n) :: nil
       | S x => StageSet.empty :: (add x)
      end) x
    | s :: b, 0 => (StageSet.add n s) :: b
    | s :: b, S x => s :: (add x n b)
    end.

  Fixpoint remove (n:stage) (B:t) : t :=
    match B with
    | nil => nil
    | s :: b => (StageSet.remove n s) :: (remove n b)
    end.

  Fixpoint get (x:var) (B:t) : StageSet.t :=
    match B, x with
    | nil, _ => StageSet.empty
    | s :: b, 0 => s
    | s :: b, S x => get x b
    end.

  Fixpoint ub (n:nat) (B:t) :=
    match B with
    | nil => true
    | s :: b => andb (StageSet.ub n s) (ub n b)
    end.

  Definition rho (n:nat) (s:StageSet.t) : bool :=
    NatSet.MSetIntern.fold (fun n r => andb (negb (Repl.rho n)) r) s (Repl.rho n).

  Definition varSet (x:nat) (n:stage) (B:t) : VarSet.t :=
    if rho n (get x B) then VarSet.singleton x
    else VarSet.empty.

  Definition bindSet (x:nat) (n:stage) : VarSet.t :=
    if Repl.rho n then VarSet.singleton x
    else VarSet.empty.

End BindingSet.

(** ** Properties *)
Module BindingSetProperties(Repl:Replacement).

  Module BindingSet := BindingSet Repl.
  Import NatSet.
  Import NatSetProperties.
  Import BindingSet.

  Lemma add_get_1:
    forall (x:var) (n:stage) (B:t),
    BindingSet.get x (BindingSet.add x n B) =
    StageSet.add n (BindingSet.get x B).
  Proof.
    intros ; generalize dependent B ; 
    induction x ; simpl ; intros.
    destruct B ; simpl.
    apply StageSetProperties.singleton_equal_add.
    reflexivity.
    destruct B ; simpl.
    specialize (IHx nil).
    assert(get x nil = StageSet.empty).
    destruct x ; reflexivity.
    rewrite H in IHx.
    rewrite <- IHx.
    clear IHx H.
    destruct x ; simpl ; reflexivity.
    apply IHx.
  Qed.

  Lemma add_get_2:
    forall (x y:var) (n:stage) (B:t), x <> y ->
    BindingSet.get x (BindingSet.add y n B) = BindingSet.get x B.
  Proof.
    intros ; generalize dependent y ;
    generalize dependent B ; 
    induction x ; simpl ; intros.
    destruct y ; [ exfalso ; auto |
    destruct B ; reflexivity ].
    destruct y.
    destruct B ; destruct x ; reflexivity.
    assert(x <> y).
    auto.
    destruct B.
    specialize (IHx nil y H0).
    assert(get x nil = StageSet.empty).
    destruct x ; reflexivity.
    rewrite H1 in IHx.
    remember (((fix add (x0 : nat) : list StageSet.MSetIntern.t :=
      match x0 with
      | 0 => StageSet.singleton n :: nil
      | S x1 => StageSet.empty :: add x1
      end) y)).
    rewrite <- IHx.
    subst.
    destruct y ; reflexivity.
    simpl ; apply IHx ; assumption.
  Qed.

  Lemma remove_get:
    forall (x:var) (n:stage) (B:t),
    BindingSet.get x (BindingSet.remove n B) =
    StageSet.remove n (BindingSet.get x B).
  Proof.
    intros ; generalize dependent B ; 
    induction x ; simpl ; intros ;
    destruct B ; simpl ;
    try(rewrite StageSetProperties.remove_empty) ;
    try(reflexivity).
    apply IHx.
  Qed.

  Lemma ub_get:
    forall (lst:t) (x:var) (n:nat),
    ub n lst = true -> StageSet.ub n (BindingSet.get x lst) = true.
  Proof.
    induction lst ; simpl ; intros.
    destruct x ; reflexivity.
    apply andb_true_iff in H ; destruct H.
    destruct x ; simpl.
    assumption.
    apply IHlst ; assumption.
  Qed.

  Lemma ub_le_1:
    forall (lst:t) (x:var) (n m:nat),
    m <= n -> ub n (add x m lst) = ub n lst.
  Proof.
    induction lst ; simpl ; intros.
    induction x ; simpl.
    rewrite andb_true_r.
    rewrite StageSetProperties.singleton_equal_add.
    rewrite <- StageSetProperties.ub_le_1 ; trivial.
    unfold add in IHx.
    destruct x ; assumption.
    
    destruct x ; simpl ;
    remember (StageSet.ub n a && ub n lst) ;
    destruct b ; symmetry in Heqb.
    apply andb_true_iff in Heqb.
    destruct Heqb.
    specialize (IHlst 0 n m H).
    rewrite H1 in IHlst.
    rewrite H1, andb_true_r.
    rewrite <- StageSetProperties.ub_le_1 ; trivial.
    apply andb_false_iff in Heqb.
    destruct Heqb.
    rewrite <- StageSetProperties.ub_le_1 ; trivial.
    apply andb_false_iff ; left.
    assumption.
    rewrite H0, andb_false_r ; trivial.

    apply andb_true_iff in Heqb.
    destruct Heqb.
    specialize (IHlst x n m H).
    rewrite H1 in IHlst.
    rewrite IHlst, H0 ; trivial.
    apply andb_false_iff in Heqb.
    destruct Heqb.
    rewrite H0, andb_false_l ; trivial.
    specialize (IHlst x n m H).
    rewrite H0 in IHlst.
    rewrite IHlst, andb_false_r ; trivial.
  Qed.

  Lemma ub_le_2:
    forall (lst:t) (n m:nat),
    m <= n -> ub m lst = true -> ub n lst = true.
  Proof.
    intros ; induction lst ; simpl in *|-*.
    reflexivity.
    apply andb_true_iff in H0.
    destruct H0.
    specialize (IHlst H1).
    rewrite IHlst, andb_true_r.
    apply StageSetProperties.ub_le_2 with (m:=m) ; trivial.
  Qed.

  Lemma ub_S:
    forall (lst:t) (n:nat),
    ub n (remove (S n) lst) = ub (S n) lst.
  Proof.
    intros ; induction lst ; simpl in *|-*.
    reflexivity.
    remember(StageSet.ub (S n) a && ub (S n) lst).
    destruct b ; symmetry in Heqb.
    apply andb_true_iff in Heqb.
    destruct Heqb.
    rewrite StageSetProperties.ub_S in H.
    apply andb_true_iff ; split.
    assumption.
    rewrite H0 in IHlst ; assumption.
    apply andb_false_iff in Heqb.
    destruct Heqb.
    rewrite StageSetProperties.ub_S in H.
    apply andb_false_iff ; left ; assumption.
    rewrite H in IHlst.
    apply andb_false_iff ; right ; assumption.
  Qed.

  Lemma rho_le:
    forall (m n:nat) (s:StageSet.t),
    StageSet.mem m s = true -> m <= n ->
    Repl.rho m = true -> rho n s = false.
  Proof.
    intros ; unfold rho.
    specialize (MSetProps.fold_rec) ; intros.
    specialize (X bool (fun s y => m <= n 
      -> StageSet.mem m s = true -> y = false) 
      (fun n0 r => negb (Repl.rho n0) && r) (Repl.rho n) s).
    apply X ; clear X ; trivial.
    intros.
    apply MSetProps.empty_is_empty_1, MSetIntern.eq_leibniz in H2.
    subst ; inversion H4.

    intros.
    case_beq_nat x m.
    rewrite H1 ; reflexivity.
    rewrite H5, andb_false_r ; trivial.
    rewrite <- MSetEqProps.add_mem_2 with (x:=x) ; trivial.
    apply MSetProps.Add_Equal, MSetIntern.eq_leibniz in H4.
    subst ; assumption.
  Qed.

  Lemma rho_le_O:
    forall (n:nat) (s:StageSet.t),
    StageSet.mem 0 s = true ->
    Repl.rho 0 = true -> rho n s = false.
  Proof.
    intros ; apply rho_le with (m:=0) ; trivial.
    omega.
  Qed.

  Lemma rho_false:
    forall (n:nat) (s:StageSet.t),
    Repl.rho n = false -> rho n s = false.
  Proof.
    unfold rho ; specialize (MSetProps.fold_rec) ; intros.
    specialize (X bool (fun s y => Repl.rho n = false -> y = false) 
      (fun n0 r => negb (Repl.rho n0) && r) (Repl.rho n) s).
    apply X ; clear X ; trivial.
    intros.
    rewrite H3, andb_false_r ; trivial.
  Qed.

  Lemma rho_false_mem:
    forall (n:nat) (s:StageSet.t),
    mem n s = true -> rho n s = false.
  Proof.
    unfold rho ; intros.
    remember(Repl.rho n).
    destruct b ; symmetry in Heqb.
    specialize (MSetEqProps.add_remove s n H) ; intros.
    apply MSetIntern.equal_spec, MSetIntern.eq_leibniz in H0.
    rewrite <- H0.
    rewrite MSetEqProps.fold_add ; auto.
    apply andb_false_iff ; left.
    apply negb_false_iff ; assumption.
    clear ; constructor ; auto.
    unfold Transitive ; intros ; subst ; auto.
    clear ; unfold Proper.
    unfold respectful ; intros.
    subst ; reflexivity.
    unfold SetoidList.transpose ; intros.
    rewrite andb_assoc.
    rewrite andb_comm with (b1:=negb (Repl.rho x)).
    rewrite <- andb_assoc ; reflexivity.
    apply MSetEqProps.remove_mem_1.
    specialize (rho_false n s Heqb) ; intros.
    unfold rho in H0 ; rewrite Heqb in H0 ; assumption.
  Qed.

  Lemma rho_le_true:
    forall (s:StageSet.t) (n:nat),
    (forall m, m <= n -> 
      (StageSet.mem m s = false \/ Repl.rho m = false)) ->
    StageSet.ub n s = true ->
    BindingSet.rho n s = Repl.rho n.
  Proof.
    intros ; unfold rho.
    specialize (MSetProps.fold_rec) ; intros.
    specialize (X bool (fun s y =>
      (forall m, m <= n -> 
      (StageSet.mem m s = false \/ Repl.rho m = false)) ->
      StageSet.ub n s = true -> y = Repl.rho n) 
      (fun n0 r => negb (Repl.rho n0) && r) (Repl.rho n) s).
    apply X ; clear X ; trivial.
    intros.
    apply MSetProps.Add_Equal, MSetIntern.eq_leibniz in H3.
    subst.
    rewrite <- H4 ; trivial.
    destruct a ; 
    [rewrite andb_true_r | rewrite andb_false_r ; trivial].

    apply StageSetProperties.ub_le_3 with (m:=x) in H0.
    specialize (H5 x H0).
    destruct H5.
    rewrite StageSetProperties.add_mem_3 in H3 ; inversion H3.
    rewrite H3 ; reflexivity.
    apply MSetIntern.mem_spec ; assumption.

    intros.
    specialize (H5 m H3) ; destruct H5 ; [left|right] ; trivial.
    apply StageSetProperties.add_mem_5 in H5.
    assumption.
    apply StageSetProperties.add_ub in H6 ; assumption.
  Qed.

  Lemma rho_O_true:
    forall (St:StageSet.t),
    StageSet.mem 0 St = false ->
    StageSet.ub 0 St = true ->
    BindingSet.rho 0 St = true.
  Proof.
   intros.
   rewrite <- Repl.rho_O.
   apply rho_le_true ; trivial.
   intros.
   inversion H1 ; left ; assumption.
  Qed.

End BindingSetProperties.

(** * Memory *)

(** ** Definitions *)

Module Type MemoryType.
  Parameter data : Type.
  Parameter default : data.
End MemoryType.

Module Memory (T:MemoryType).

  Import T.

  Module Loc.
    Definition t : Set := nat.
  End Loc.

  Definition t : Type := list data.

  Definition empty : t := nil.

  Fixpoint set (l:Loc.t) (d:data) (M:t) : t :=
    match l, M with
      | O, d' :: M => d :: M
      | O, nil => d :: nil
      | S l, nil => default :: set l d nil
      | S l, d' :: M => d' :: set l d M
    end.

  Function get (l:Loc.t) (M:t) : data :=
    nth l M default.

  Definition fresh (M:t) : Loc.t := length M.
  
End Memory.

(** ** Properties *)

Module MemoryProperties (T:MemoryType).

End MemoryProperties.
