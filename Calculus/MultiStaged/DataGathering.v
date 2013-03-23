Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Relations.Relation_Definitions.
Require Import "Misc/Tactics".
Require Import "Calculus/Sets".
Require Import "Calculus/Definitions".
Require Import "Calculus/Monad".
Require Import "Calculus/MultiStaged/Definitions".

Module Type DataGathering (R:Replacement) 
  (S:ReplacementCalculus R).

  Parameter dg_t: Type.
  Parameter dg_empty: dg_t.
  Parameter dg_eabs: dg_t -> S.var -> dg_t.
  Parameter dg_efix: dg_t -> S.var -> S.var -> dg_t.
  Parameter dg_eapp_l: dg_t -> dg_t.
  Parameter dg_eapp_r: dg_t -> dg_t.
  Parameter dg_eref: dg_t -> dg_t.
  Parameter dg_ederef: dg_t -> dg_t.
  Parameter dg_eassign_l: dg_t -> dg_t.
  Parameter dg_eassign_r: dg_t -> dg_t.
  Parameter dg_erun: dg_t -> dg_t.
  Parameter dg_elift: dg_t -> dg_t.
  Parameter dg_ebox: dg_t -> dg_t.

End DataGathering.

Module Type DataGatheringPredicates (R:Replacement) 
  (S:ReplacementCalculus R) (DG:DataGathering R S).

  Import DG.

  (**
  All predicates aim to express well-formness properties
  of data gathering values. As we have no information
  about data gathering types, we need those properties
  in a quite complicated way, controlling the tree
  of applications of abstract operations over those types.
  *)

  (**
  dg_comp dg1 dg2 is true iff dg2 is resulting from dg1
  by composing it with arbitrary number of dg_.. operations.
  *)
  Inductive dg_comp : dg_t -> dg_t -> Prop :=
  | DgCompId : forall (dg:dg_t), dg_comp dg dg
  | DgCompEAbs : forall (dg1 dg2:dg_t) (x:S.var),
    dg_comp dg1 dg2 -> dg_comp dg1 (dg_eabs dg2 x)
  | DgCompEFix : forall (dg1 dg2:dg_t) (f x:S.var),
    dg_comp dg1 dg2 -> dg_comp dg1 (dg_efix dg2 f x)
  | DgCompEAppL : forall (dg1 dg2:dg_t),
    dg_comp dg1 dg2 -> dg_comp dg1 (dg_eapp_l dg2)
  | DgCompEAppR : forall (dg1 dg2:dg_t),
    dg_comp dg1 dg2 -> dg_comp dg1 (dg_eapp_r dg2)
  | DgCompERef : forall (dg1 dg2:dg_t),
    dg_comp dg1 dg2 -> dg_comp dg1 (dg_eref dg2)
  | DgCompEDeref : forall (dg1 dg2:dg_t),
    dg_comp dg1 dg2 -> dg_comp dg1 (dg_ederef dg2)
  | DgCompEAssignL : forall (dg1 dg2:dg_t),
    dg_comp dg1 dg2 -> dg_comp dg1 (dg_eassign_l dg2)
  | DgCompEAssignR : forall (dg1 dg2:dg_t),
    dg_comp dg1 dg2 -> dg_comp dg1 (dg_eassign_r dg2)
  | DgCompERun : forall (dg1 dg2:dg_t),
    dg_comp dg1 dg2 -> dg_comp dg1 (dg_erun dg2)
  | DgCompELift : forall (dg1 dg2:dg_t),
    dg_comp dg1 dg2 -> dg_comp dg1 (dg_elift dg2).

  (**
  dg_comp_lst is the list closure of dg_comp. It checks pairwise
  wether elements of lists are obtained from each other
  by arbitrary composition of dg_... operations.
  *)
  Inductive dg_comp_lst (dg:dg_t) : (list dg_t) -> Prop :=
  | DgCompLstNil : dg_comp_lst dg nil
  | DgCompLstCons : forall (dg1:dg_t) (dgs:list dg_t),
    dg_comp_lst dg1 dgs -> dg_comp (dg_ebox dg1) dg -> dg_comp_lst dg (dg1::dgs).

  (**
  dg_nth_empty dg n checks whether dg is obtained
  by applying n occurrences of dg_ebox (modulo dg_comp).
  *)
  Inductive dg_nth_empty : dg_t -> nat -> Prop :=
  | DgNthEmpty0 : dg_nth_empty dg_empty 0
  | DgNthEmptyS : forall (dg1 dg2:dg_t) (n:nat),
      dg_nth_empty dg1 n -> dg_comp (dg_ebox dg1) dg2 -> 
      dg_nth_empty dg2 (S n).

End DataGatheringPredicates.

Module Type DataGatheringRequirements (R:Replacement) 
  (S:ReplacementCalculus R) (DG:DataGathering R S)
  (DGP:DataGatheringPredicates R S DG).

  Import DG.
  Import DGP.

  Parameter dg_eabs_empty : 
    forall (x:S.var), dg_eabs dg_empty x = dg_empty.

  Parameter dg_efix_empty :
    forall (f x:S.var), dg_efix dg_empty f x = dg_empty.

  Parameter dg_eapp_l_empty : dg_eapp_l dg_empty = dg_empty.
  Parameter dg_eapp_r_empty : dg_eapp_r dg_empty = dg_empty.
  Parameter dg_eref_empty : dg_eref dg_empty = dg_empty.
  Parameter dg_ederef_empty : dg_ederef dg_empty = dg_empty.
  Parameter dg_eassign_l_empty : dg_eassign_l dg_empty = dg_empty.
  Parameter dg_eassign_r_empty : dg_eassign_r dg_empty = dg_empty.
  Parameter dg_erun_empty : dg_erun dg_empty = dg_empty.
  Parameter dg_elift_empty : dg_elift dg_empty = dg_empty.

  Parameter dg_ebox_empty :
    forall (dg:dg_t) (n:nat), R.rho (S n) = true ->
    dg_nth_empty dg n -> dg_ebox dg = dg_empty.

End DataGatheringRequirements.

Module DataGatheringProperties (R:Replacement)
  (S:ReplacementCalculus R) (DG:DataGathering R S) 
  (DGP:DataGatheringPredicates R S DG)
  (DGR:DataGatheringRequirements R S DG DGP).

  Import DG.
  Import DGP.
  Import DGR.

  Definition valid_dgs (n:nat) (dg:dg_t) (dgs:list dg_t) :=
    n <= length dgs /\
    dg_comp_lst dg dgs /\
    forall (m:nat), m <= n -> R.rho m = true -> 
    match (n - m) with
    | 0 => dg = dg_empty
    | S n => nth n dgs dg_empty = dg_empty
    end.

  Lemma dg_comp_trans:
    forall (dg1 dg2 dg3:dg_t),
    dg_comp dg1 dg2 -> dg_comp dg2 dg3 -> dg_comp dg1 dg3.
  Proof.
    intros ; generalize dependent dg1.
    induction H0 ; intros ; auto ;
    try(constructor ; auto ; fail).
  Qed.

  Lemma dg_comp_lst_trans:
    forall (dg1 dg2:dg_t) (dgs:list dg_t),
    dg_comp dg1 dg2 -> dg_comp_lst dg1 dgs -> dg_comp_lst dg2 dgs.
  Proof.
    intros ; generalize dependent dgs.
    inverts H ; intros ; auto ;
    try(destruct dgs ; inverts H1 ; constructor ; auto ;
    apply dg_comp_trans with (dg2:=dg1) ; auto ;
    constructor ; auto).
  Qed.

  Lemma dg_comp_empty_ind:
    forall (dg1 dg2:dg_t), dg_comp dg1 dg2 -> dg1 = dg_empty -> dg2 = dg_empty.
  Proof.
    assert(dg_empty = dg_empty) as Eq1.
    reflexivity.

    intros ; induction H ; subst ; auto ~ ;
    specialize (IHdg_comp Eq1) ; subst.
    apply dg_eabs_empty.
    apply dg_efix_empty.
    apply dg_eapp_l_empty.
    apply dg_eapp_r_empty.
    apply dg_eref_empty.
    apply dg_ederef_empty.
    apply dg_eassign_l_empty.
    apply dg_eassign_r_empty.
    apply dg_erun_empty.
    apply dg_elift_empty.
  Qed.

  Lemma dg_comp_empty:
    forall (dg:dg_t), dg_comp dg_empty dg -> dg = dg_empty.
  Proof.
     intros ; apply dg_comp_empty_ind with (dg1:=dg_empty) ; auto ~.
  Qed.

  Lemma valid_dgs_trans:
    forall (n:nat) (dg1 dg2:dg_t) (dgs:list dg_t),
    dg_comp dg1 dg2 -> valid_dgs n dg1 dgs -> valid_dgs n dg2 dgs.
  Proof.
    unfold valid_dgs ; intros ; repeat(split) ; auto ~ ; intros.
    destruct H0 ; auto ~.
    destruct H0 ; destruct H1.
    apply dg_comp_lst_trans with (dg1:=dg1) ; auto ~.
    destruct H0 ; destruct H3.
    specialize (H4 m H1 H2).
    destruct (n-m) ; subst ; auto ~.
    apply dg_comp_empty ; auto ~.
  Qed.

  Lemma valid_dgs_eunbox:
    forall (n:nat) (dg1 dg2:dg_t) (dgs:list dg_t),
    valid_dgs (S n) dg1 (dg2::dgs) -> valid_dgs n dg2 dgs.
  Proof.
    unfold valid_dgs ; intros ; repeat(split) ; auto ~ ; intros.
    destruct H ; simpl in *|-* ; omega.
    destruct H ; destruct H0 ; inverts H0 ; auto ~.
    destruct H ; destruct H2.
    assert(m <= S n) as Eq1.
    omega.
    specialize (H3 m Eq1 H1).
    rewrite <- minus_Sn_m in H3 ; auto ~.
    destruct (n - m) ; auto ~.
  Qed.

  Lemma dg_nth_empty_lst:
    forall (n:nat) (dg:dg_t) (dgs:list dg_t),
    length dgs >= n ->
    dg_comp_lst dg dgs ->
    nth n (dg::dgs) dg_empty = dg_empty -> 
    dg_nth_empty dg n.
  Proof.
    induction n ; simpl ; intros.
    subst ; constructor.
    destruct dgs.
    exfalso ; simpl in *|-* ; omega.
    simpl in H ; apply le_S_n in H.
    inverts H0.
    specialize (IHn d dgs H H4).
    apply DgNthEmptyS with (dg1:=d) ; auto ~.
  Qed.

  Lemma valid_dgs_ebox:
    forall (n:nat) (dg:dg_t) (dgs:list dg_t),
    valid_dgs n dg dgs -> valid_dgs (S n) (dg_ebox dg) (dg :: dgs).
  Proof.
    unfold valid_dgs ; intros ; repeat(split) ; auto ~ ; intros.
    simpl ; omega.
    destruct H ; destruct H0 ; constructor ; auto ~ ; repeat(constructor).
    case_beq_nat m (S n).
    rewrite minus_diag.
    apply dg_ebox_empty with (n:=n) ; auto ~.
    destruct H ; destruct H2.
    assert(0 <= n) as Eq1.
    omega.
    specialize (H3 0 Eq1 R.rho_O).
    apply dg_nth_empty_lst with (dgs:=dgs) ; auto ~.
    rewrite <- minus_n_O in H3 ; destruct n ; auto ~.
    assert(m <= n) as Eq1.
    omega.
    rewrite <- minus_Sn_m ; auto ~.
    destruct H ; destruct H2 ; specialize (H3 m Eq1 H1).
    destruct (n-m) ; auto ~.
  Qed.

  Lemma dg_valid_dgs_nil: valid_dgs 0 dg_empty nil.
  Proof.
    repeat(split) ; intros ; auto ~.
    constructor.
  Qed.

  Lemma dg_valid_dgs_empty: 
    forall (dg:dg_t) (dgs:list dg_t),
    valid_dgs 0 dg dgs -> dg = dg_empty.
  Proof.
    intros ; destruct H.
    destruct H0.
    specialize (H1 0) ; simpl in *|-*.
    apply H1 ; auto.
    apply R.rho_O.
  Qed.
  
End DataGatheringProperties.
