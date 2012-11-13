Require Import Coq.Arith.Arith.
Require Import Coq.Arith.MinMax.
Require Import Coq.Bool.Bool.
Require Import Coq.omega.Omega.
Require Import "Misc/Tactics".
Require Import "Misc/Relation".
Require Import "Calculus/Sets".
Require Import "Calculus/Terminology".
Require Import "Calculus/MultiStaged/Definitions".

(** * Calculus Properties *)
Module CalculusProperties (Repl:Replacement).

  Module Calculus := Calculus Repl.
  Module Terminology := StagedTerminology Calculus.
  Import Calculus.CRaw.
  Import Calculus.
  Import Terminology.

  (** ** Values *)

  Lemma svalue_n_Sn_O:
    forall (n:nat) (e:expr),
    svalue n e -> svalue (S n) e \/ n = 0.
  Proof.
   induction 1 ; intros ;
   try(left ; constructor ; fail) ;
   try(destruct IHsvalue ; 
     [left ; constructor ; trivial | inversion H0]) ;
   try(right ; reflexivity) ;
   try(
     destruct IHsvalue1 ; try(inversion H1 ; fail) ;
     destruct IHsvalue2 ; try(inversion H2 ; fail) ;
     left ; constructor ; trivial
   ).
  Qed.

  Lemma svalue_Sn_SSn:
    forall (n:nat) (e:expr),
    svalue (S n) e -> svalue (S (S n)) e.
  Proof.
    intros.
    apply svalue_n_Sn_O in H.
    destruct H ; [assumption|inversion H].
  Qed.

  Lemma svalue_not_sprogresses:
    forall (n:nat) (M:Memory.t) (v:expr),
    svalue n v -> not_sprogresses n (M,v).
  Proof.
    unfold not_sprogresses ;
    induction 1 ; red ; intros ;
    try(inversion H ; fail) ;
    try(inversion H0 ; subst ;
      try(apply IHsvalue in H5) ; 
      try(apply IHsvalue in H6) ;
      try(apply IHsvalue in H7) ; contradiction) ;
    try(inversion H1 ; subst ;
      [apply IHsvalue1 in H7 | apply IHsvalue2 in H8] ;
      contradiction).
  Qed.

  (** ** Partial Functions *)
  
  Lemma sstep_partial_function:
    forall (n:nat), partial_function (sstep n).
  Proof.
    unfold partial_function ; intros.
    generalize dependent y2.
    induction H ; intros ;

    (* App L, Assign L *)
    try(inversion H0 ; subst ;
    try(
      specialize (IHsstep (N0, e5) H6) ; 
      inversion IHsstep ; subst ; reflexivity
    ) ;
    apply svalue_not_sprogresses in H ; try(contradiction) ;
    try(trivial) ; constructor ; fail) ;

    (* App R, Assign R *)
    try(inversion H1 ; subst ;
    try(
      specialize (IHsstep (N0, e3) H8) ;
      inversion IHsstep ; subst ; reflexivity
    ) ;
    try(apply svalue_not_sprogresses in H0) ;
    try(apply svalue_not_sprogresses in H7) ;
    try(contradiction) ; try(trivial) ; fail) ;

    (* App Abs, App Fix, Assign O *)
    try(inversion H0 ; subst ; try(reflexivity) ;
    try(apply svalue_not_sprogresses in H6) ;
    try(apply svalue_not_sprogresses in H7) ;
    try(contradiction) ; try(trivial) ; constructor ; fail) ;

    (* Ref, Deref, Box, Unbox, Run *)
    try(inversion H0 ; subst ; try(
    specialize (IHsstep (N0, e3) H5) ;
    inversion IHsstep ; subst ; reflexivity ) ;
    apply svalue_not_sprogresses in H ; try(contradiction) ;
    try(constructor) ; trivial ; fail) ;

    (* Unbox 0, Box 0 , Ref 0, Deref 0 *)
    try(inversion H0 ; subst ; try(reflexivity) ;
    try(apply svalue_not_sprogresses in H5) ;
    try(apply svalue_not_sprogresses in H4) ; try(contradiction) ;
    try(constructor) ; trivial ; fail) ;

    (* Abs, Fix *)
    inversion H0 ; subst ;
    try(specialize (IHsstep (N0, e3) H6)) ;
    try(specialize (IHsstep (N0, e3) H7)) ;
    inversion IHsstep ; subst ; reflexivity.
  Qed.

  (** ** Depth *)
  Lemma depth_sstep:
    forall (M1:Memory.t) (e1:expr)
    (M2:Memory.t) (e2:expr) (n:nat),
    depth e1 < n -> (M1, e1) ⊨ n ⇒ (M2, e2) ->
    e1 = e2 /\ M1 = M2.
  Proof.
    induction e1 ; simpl ; intros ;
    destruct n ; try(inversion H ; fail) ;

    (* EConst, ELoc, EVar *)
    try(inversion H0 ; fail) ;

    (* EAbs, EFix *)
    try(inversion H0 ; subst ;
    specialize (IHe1 M2 e3 (S n) H H3) ;
    destruct IHe1 ; subst ; auto ; fail) ;

    (* ERef, EDeref, ERun, ELift *)
    try(inversion H0 ; subst ;
    specialize (IHe1 M2 e3 (S n) H H3) ;
    destruct IHe1 ; subst ; auto ; fail) ;

    (* EApp, EAssign *)
    try(apply max_lub_lt_iff in H ; destruct H ;
    inversion H0 ; subst ; [
    specialize (IHe1_1 M2 e3 (S n) H H4) ;
    destruct IHe1_1 ; subst ; auto |
    specialize (IHe1_2 M2 e0 (S n) H1 H9) ;
    destruct IHe1_2 ; subst ; auto ] ; fail).

    (* EBox *)
    inversion H0 ; subst.
    destruct (depth e1) ; simpl in H ;
    [ assert(0 < S (S n)) ; auto |
     assert(S n0 < S (S n)) ; try(omega)] ;
    specialize (IHe1 M2 e3 (S (S n)) H1 H3) ;
    destruct IHe1 ; subst ; auto.
    
    (* EUnbox *)
    inversion H0 ; subst.
    apply lt_S_n in H.
    specialize (IHe1 M2 e3 n H H3).
    destruct IHe1 ; subst ; auto.
    exfalso ; omega.
  Qed.

  Lemma depth_svalue:
    forall (e:expr) (n:nat),
    depth e < (S n) <-> svalue (S n) e.
  Proof.
    induction e ; split ; intros ; simpl in *|-* ;
    try(constructor ; fail) ;
    try(omega) ;
    try(
      apply IHe in H ;
      constructor ; assumption
    ) ;
    try(
      inversion H ; subst ; 
      apply IHe ; assumption
    ) ;
    try(
      constructor ;
      [apply IHe1 | apply IHe2] ;
      apply max_lub_lt_iff in H ; 
      destruct H ; assumption
    ) ;
    try(
      inversion H ; subst ;
      apply max_lub_lt ; 
      [apply IHe1 | apply IHe2] ; 
      assumption
   ).

   constructor ; apply IHe ;
   omega.

   inversion H ; subst ;
   apply IHe in H2 ; omega.

   destruct n ;
   [exfalso | constructor ; apply IHe] ; 
   omega.

   inversion H ; subst.
   apply IHe in H2 ; omega.
  Qed.

  (** ** Fresh **)
  Lemma fresh_bv:
    forall (x:var) (e:expr) (n:nat),
    VarSet.mem x (bv n e) = true -> x < fresh e.
  Proof.
    induction e ; intros ; simpl in *|-* ;

    (* Case EVar, ELoc, EConst *)
    try(inversion H ; fail) ;

    (* Case ERef, EDeref *)
    try(specialize (IHe n) ; tauto ; fail) ;

    (* Case EApp, EAssign *)
    try(
      rewrite VarSetProperties.union_mem in H ;
      apply orb_prop in H ;
      specialize (IHe1 n) ;
      specialize (IHe2 n) ;
      apply max_lt_iff ;
      tauto ; fail).

    (* Case EAbs *)
    rewrite VarSetProperties.union_mem in H ;
    apply orb_prop in H ;
    destruct H ; [
    unfold BindingSet.bindSet in H ;
    destruct (Repl.rho n) ; [
    apply VarSetProperties.singleton_mem in H ;
    subst ;
    destruct (fresh e) ; [auto |] ; 
    apply le_trans with (m:= S x) ;
    [auto | apply le_n_S ; apply le_max_l]
    | ] ; inversion H | 
    apply IHe in H ;
    destruct (fresh e) ; [
    inversion H | 
    apply le_trans with (m:= S v0) ; 
    [auto | apply le_n_S ; apply le_max_r]]].

    (* Case EFix *)
    rewrite VarSetProperties.union_mem in H.
    apply orb_prop in H.
    destruct H.
    
    unfold BindingSet.bindSet in H ;
    destruct (Repl.rho n) ; [
    apply VarSetProperties.singleton_mem in H ;
    subst ;
    destruct (fresh e) ; [auto |] ; 
    apply le_trans with (m:= S x) ; auto ;
    apply le_n_S ; apply le_max_l |
    inversion H ].

    rewrite VarSetProperties.union_mem in H ;
    apply orb_prop in H ;
    destruct H.

    unfold BindingSet.bindSet in H ;
    destruct (Repl.rho n) ; [
    apply VarSetProperties.singleton_mem in H ;
    subst ;
    destruct (fresh e) ; [auto |] ; 
    apply le_trans with (m:= S x) ; auto ;
    [apply le_n_S ; apply le_max_r |
    apply le_trans with (m:= S (max x v0)) ; auto ;
    [apply le_n_S ; apply le_max_l |
    apply le_n_S ; apply le_max_r ]] | inversion H].

    apply IHe in H ;
    destruct (fresh e) ; [
    inversion H | 
    apply le_trans with (m:= S v1)] ; auto ;
    apply le_n_S ; apply le_trans with (m:= (max v0 v1)) ; auto ;
    apply le_max_r.

    (* Case EBox *)
    specialize (IHe (S n)).
    tauto.

    (* Case EUnbox *)
    specialize (IHe (pred n)).
    tauto.
  Qed.

End CalculusProperties.

(** * Lisp-Like Calculus Properties *)
Module LispLikeCalculusProperties.

  Module BindingSetProperties := 
    BindingSetProperties LispLikeCalculus.
  Import LispLikeCalculus.
  Import LispLikeCalculus.CRaw.
  Import LispLikeReplacement.

  (** ** Explicit Lisp-Like Substitution Function *)
  Fixpoint ll_subst (n:nat) (x:var) (e v:expr) :=
    match e with
    | EConst _ => e
    | EVar y =>
        if andb (beq_nat x y) (beq_nat n 0) then v else e
    | EAbs y e => EAbs y
        (if andb (beq_nat x y) (beq_nat n 0) 
        then e else ll_subst n x e v)
    | EFix f y e => EFix f y
        (if andb (orb (beq_nat x f) (beq_nat x y)) (beq_nat n 0) 
        then e else ll_subst n x e v)
    | EApp e1 e2 => EApp (ll_subst n x e1 v) (ll_subst n x e2 v)
    | ELoc l => ELoc l
    | ERef e => ERef (ll_subst n x e v)
    | EDeref e => EDeref (ll_subst n x e v)
    | EAssign e1 e2 => EAssign (ll_subst n x e1 v) (ll_subst n x e2 v)
    | EBox e => EBox (ll_subst (S n) x e v)
    | EUnbox e => EUnbox (ll_subst (pred n) x e v)
    | ERun e => ERun (ll_subst n x e v)
    | ELift e => ELift (ll_subst n x e v)
    end.

  Lemma ssubst_ll_rho_O:
    forall (e v:expr) (St:StageSet.t) (n:nat) (x:var),
    StageSet.mem 0 St = true ->
    depth e <= n ->
    ssubst n St x e v = e.
  Proof.
    induction e ; simpl ; intros ;
    try(rewrite IHe) ;
    try(rewrite IHe1, IHe2) ;
    try(omega) ;
    try(apply max_lub_r in H0 ; assumption) ;
    try(apply max_lub_l in H0 ; assumption) ;
    try(reflexivity) ;
    try(assumption).

    (* Var *)
    assert(BindingSet.rho n St = false).
    apply BindingSetProperties.rho_le_O ; trivial.
    rewrite H1, andb_false_r ; reflexivity.

    (* Abs *)
    destruct (beq_nat x v).
    apply StageSetProperties.add_mem_2 ; assumption.
    assumption.
    (* Fix *)
    destruct (beq_nat x v || beq_nat x v0).
    apply StageSetProperties.add_mem_2 ; assumption.
    assumption.
    destruct n.
    exfalso ; omega.
    rewrite StageSetProperties.remove_mem_1.
    assumption.
    omega.
  Qed.

  Lemma ssubst_ll_subst:
    forall (e v:expr) (St:StageSet.t) (n:nat) (x:var),
    StageSet.ub n St = true -> 
    StageSet.mem 0 St = false ->
    depth e <= n ->
    ssubst n St x e v = ll_subst n x e v.
  Proof.
    induction e ; simpl ; intros ;
    try(rewrite IHe1, IHe2) ;
    try(omega) ;
    try(apply max_lub_r in H1 ; assumption) ;
    try(apply max_lub_l in H1 ; assumption) ;
    try(reflexivity) ;
    try(assumption) ;
    try(rewrite IHe ; 
    try(assumption) ; try(reflexivity) ; fail).

    (* Var *)
    destruct n.
    rewrite <- beq_nat_refl.
    assert(BindingSet.rho 0 St = true).
    apply BindingSetProperties.rho_O_true ; trivial.
    rewrite H2, andb_true_r ; reflexivity.
    assert(beq_nat (S n) 0 = false).
    apply beq_nat_false_iff ; omega.
    rewrite H2, andb_false_r.
    assert(BindingSet.rho (S n) St = false).
    apply BindingSetProperties.rho_false.
    reflexivity.
    rewrite H3, andb_false_r ; reflexivity.

    (* Abs *)
    destruct n.
    rewrite <- beq_nat_refl, andb_true_r.
    destruct (beq_nat x v).
    rewrite ssubst_ll_rho_O ; try(trivial).
    apply StageSetProperties.add_mem_3.
    rewrite IHe ; try(reflexivity) ; assumption.
    assert(beq_nat (S n) 0 = false).
    apply beq_nat_false_iff ; omega.
    rewrite H2, andb_false_r.
    destruct (beq_nat x v) ; rewrite IHe ; 
    try(assumption) ; try(reflexivity).
    rewrite <- StageSetProperties.ub_le_1 ; auto.
    rewrite StageSetProperties.add_mem_4.
    assumption.
    auto.

    (* Fix *)
    destruct n.
    rewrite <- beq_nat_refl, andb_true_r.
    destruct (beq_nat x v).
    rewrite ssubst_ll_rho_O ; trivial.
    rewrite orb_true_l.
    apply StageSetProperties.add_mem_3.
    rewrite orb_false_l.
    destruct (beq_nat x v0).
    rewrite ssubst_ll_rho_O ; trivial.
    apply StageSetProperties.add_mem_3.
    rewrite IHe ; try(reflexivity) ; assumption.
    assert(beq_nat (S n) 0 = false).
    apply beq_nat_false_iff ; omega.
    rewrite H2, andb_false_r.
    destruct (beq_nat x v) ; rewrite IHe ; 
    try(assumption) ; try(reflexivity).
    rewrite orb_true_l.
    rewrite <- StageSetProperties.ub_le_1 ; auto.
    rewrite orb_true_l.
    rewrite StageSetProperties.add_mem_4 ; auto.
    rewrite orb_false_l.
    destruct (beq_nat x v0).
    rewrite <- StageSetProperties.ub_le_1 ; auto.
    assumption.
    rewrite orb_false_l.
    destruct (beq_nat x v0).
    rewrite StageSetProperties.add_mem_4 ; auto.
    assumption.

    (* Box *)
    rewrite IHe ; try(reflexivity) ; try(assumption).
    apply StageSetProperties.ub_le_2 with (m:=n) ; auto.
    omega.

    (* Unbox *)
    destruct n ; [exfalso ; omega|].
    simpl ; rewrite IHe ; try(reflexivity) ; try(assumption).
    rewrite <- StageSetProperties.ub_S ; auto.
    rewrite StageSetProperties.remove_mem_1 ; auto.
    omega.
  Qed.

  Lemma ssubst_ll_subst_O:
    forall (e v:expr) (x:var),
    depth e = 0 ->
    ssubst 0 StageSet.empty x e v = ll_subst 0 x e v.
  Proof.
    intros ; rewrite ssubst_ll_subst ; 
    auto ; omega.
  Qed.

  (** ** Explicit Lisp-Like Free Variables Function *)
  Fixpoint ll_fv (n:nat) (e:expr) : VarSet.t :=
    match e with
    | EConst _ => VarSet.empty
    | EVar x => match n with
        | 0 => VarSet.singleton x
        | S _ => VarSet.empty
        end
    | EAbs x e => match n with
        | 0 => VarSet.remove x (ll_fv n e)
        | S _ => ll_fv n e
        end
    | EFix f x e => match n with
        | 0 => VarSet.remove x (VarSet.remove f (ll_fv n e))
        | S _ => ll_fv n e
        end
    | EApp e1 e2 => VarSet.union (ll_fv n e1) (ll_fv n e2)
    | ELoc _ => VarSet.empty
    | ERef e => ll_fv n e
    | EDeref e => ll_fv n e
    | EAssign e1 e2 => VarSet.union (ll_fv n e1) (ll_fv n e2)
    | EBox e => ll_fv (S n) e
    | EUnbox e => ll_fv (pred n) e
    | ERun e => ll_fv n e
    | ELift e => ll_fv n e
    end.

  Lemma fv_ll_rho_O:
    forall (e:expr) (B:BindingSet.t) (n:nat) (x:var),
    StageSet.mem 0 (BindingSet.get x B) = true ->
    depth e <= n ->
    VarSet.mem x (fv n B e) = false.
  Proof.
    induction e ; simpl ; intros ;

    try(rewrite IHe with (n:=n) ; trivial ; fail) ;
    try(
      rewrite VarSetProperties.union_mem, orb_false_iff ;
      rewrite max_lub_iff in H0 ; destruct H0 ; split ; 
      [rewrite IHe1 with (n:=n) | rewrite IHe2 with (n:=n)] ; 
      trivial ; fail) ;
    try(destruct x ; reflexivity ; fail).
 
    (* Var *)
    unfold BindingSet.varSet, rho.
    case_beq_nat n 0 ; simpl.
    case_beq_nat v x.
    rewrite BindingSetProperties.rho_le_O ; trivial.
    destruct (BindingSet.rho 0 (BindingSet.get v B)) ; trivial.
    rewrite VarSetProperties.singleton_equal_add.
    apply VarSetProperties.add_mem_4 ; auto.
    destruct n ; [exfalso ; auto|].
    rewrite BindingSetProperties.rho_false ; trivial.

    (* Abs *)
    rewrite IHe with (n:=n) ; trivial.
    case_beq_nat v x.
    rewrite BindingSetProperties.add_get_1.
    case_beq_nat n 0.
    apply StageSetProperties.add_mem_3.
    rewrite StageSetProperties.add_mem_4 ; auto.
    rewrite BindingSetProperties.add_get_2 ; auto.

    (* Fix *)
    rewrite IHe with (n:=n) ; trivial.
    assert(Sets.NatSet.MSetIntern.mem 0
      (BindingSetProperties.BindingSet.get x 
      (BindingSet.add v0 n B)) = true).
    case_beq_nat v0 x.
    rewrite BindingSetProperties.add_get_1.
    case_beq_nat n 0.
    apply StageSetProperties.add_mem_3.
    rewrite StageSetProperties.add_mem_4 ; auto.
    rewrite BindingSetProperties.add_get_2 ; auto.

    case_beq_nat v x.
    rewrite BindingSetProperties.add_get_1.
    case_beq_nat n 0.
    apply StageSetProperties.add_mem_3.
    rewrite StageSetProperties.add_mem_4 ; auto.
    rewrite BindingSetProperties.add_get_2 ; auto.

    (* Box *)
    apply IHe ; auto ; omega.

    (* Unbox *)
    destruct n.
    inversion H0.
    apply le_S_n in H0.
    apply IHe ; auto.
    rewrite BindingSetProperties.remove_get.
    rewrite StageSetProperties.remove_mem_1 ; auto.
  Qed.

  Lemma fv_ll_fv:
    forall (e:expr) (B:BindingSet.t) (x:var) (n:nat),
    BindingSet.ub n B = true ->
    StageSet.mem 0 (BindingSet.get x B) = false ->
    depth e <= n ->
    StageSet.mem x (fv n B e) = StageSet.mem x (ll_fv n e).
  Proof.
    induction e ; simpl ; intros ;
    (* Const, Loc *)
    try(reflexivity) ;
    (* Ref, Deref, Lift, Run *)
    try(apply IHe ; trivial ; fail) ;
    (* App, Assign *)
    try(repeat (rewrite VarSetProperties.union_mem) ;
    rewrite IHe1, IHe2 ; trivial ;
    [apply max_lub_r in H1 | apply max_lub_l in H1 ];
    trivial ; fail).

    (* Var *)
    destruct n ;
    unfold BindingSet.varSet, rho.
    case_beq_nat v x.
    rewrite BindingSetProperties.rho_O_true ; trivial.
    apply BindingSetProperties.ub_get ; trivial.
    destruct (BindingSet.rho 0 (BindingSet.get v B)).
    reflexivity.
    rewrite VarSetProperties.singleton_equal_add.
    rewrite VarSetProperties.add_mem_4 ; trivial.
    rewrite BindingSetProperties.rho_false ; trivial. 

    (* Abs *)
    destruct n.
    case_beq_nat v x.
    rewrite VarSetProperties.remove_mem_2.
    apply fv_ll_rho_O ; trivial.
    rewrite BindingSetProperties.add_get_1.
    apply StageSetProperties.add_mem_3.
    rewrite StageSetProperties.remove_mem_1 ; trivial.
    rewrite IHe ; trivial.
    rewrite BindingSetProperties.ub_le_1 ; trivial.
    rewrite BindingSetProperties.add_get_2 ; auto.

    rewrite IHe ; trivial.
    rewrite BindingSetProperties.ub_le_1 ; trivial.
    case_beq_nat v x.
    rewrite BindingSetProperties.add_get_1.
    rewrite StageSetProperties.add_mem_4 ; auto.
    rewrite BindingSetProperties.add_get_2 ; auto.

    (* Fix *)
    destruct n.
    case_beq_nat v0 x.
    rewrite VarSetProperties.remove_mem_2.
    apply fv_ll_rho_O ; trivial.
    case_beq_nat x v.
    rewrite BindingSetProperties.add_get_1.
    apply StageSetProperties.add_mem_3.
    rewrite BindingSetProperties.add_get_2 ; trivial.
    rewrite BindingSetProperties.add_get_1.
    apply StageSetProperties.add_mem_3 ; auto.

    rewrite StageSetProperties.remove_mem_1 ; trivial.
    case_beq_nat v x.
    rewrite VarSetProperties.remove_mem_2.
    apply fv_ll_rho_O ; trivial.
    rewrite BindingSetProperties.add_get_1.
     apply StageSetProperties.add_mem_3.
    rewrite StageSetProperties.remove_mem_1 ; trivial.
    rewrite IHe ; trivial.
    rewrite BindingSetProperties.ub_le_1 ; trivial.
    rewrite BindingSetProperties.ub_le_1 ; trivial.
    rewrite BindingSetProperties.add_get_2 ; auto.
    rewrite BindingSetProperties.add_get_2 ; auto.

    rewrite IHe ; trivial.
    rewrite BindingSetProperties.ub_le_1 ; trivial.
    rewrite BindingSetProperties.ub_le_1 ; trivial.
    case_beq_nat v x.
    rewrite BindingSetProperties.add_get_1.
    rewrite StageSetProperties.add_mem_4 ; auto.
    case_beq_nat v0 x.
    rewrite BindingSetProperties.add_get_1.
    rewrite StageSetProperties.add_mem_4 ; auto.
    rewrite BindingSetProperties.add_get_2 ; auto.
    rewrite BindingSetProperties.add_get_2 ; auto.
    case_beq_nat v0 x.
    rewrite BindingSetProperties.add_get_1.
    rewrite StageSetProperties.add_mem_4 ; auto.
    rewrite BindingSetProperties.add_get_2 ; auto.

    (* Box *)
    apply IHe ; trivial.
    apply BindingSetProperties.ub_le_2 with (m:=n) ; auto.
    omega.

    (* Unbox *)
    apply IHe ; trivial.
    destruct n ; simpl.
    inversion H1.
    rewrite BindingSetProperties.ub_S ; assumption.
    rewrite BindingSetProperties.remove_get.
    apply StageSetProperties.remove_mem_3 ; assumption.
    omega.
  Qed.

  Lemma fv_ll_fv_O:
    forall (e:expr) (n:nat),
    depth e = 0 ->
    fv 0 BindingSet.empty e = ll_fv 0 e.
  Proof.
    intros.
    apply StageSetProperties.equal_mem_1 ; intros.
    apply fv_ll_fv ; auto.
    destruct m ; simpl ; reflexivity.
    omega.
  Qed.

  (** ** Explicit Lisp-Like Bounded Variables Function *)
  Fixpoint ll_bv (n:nat) (e:expr) : VarSet.t :=
    match e with
    | EConst _ => VarSet.empty
    | EVar x => VarSet.empty
    | EAbs x e => match n with
        | 0 => VarSet.add x (ll_bv n e)
        | S _ => ll_bv n e
        end
    | EFix f x e => match n with
        | 0 => VarSet.add f (VarSet.add x (ll_bv n e))
        | S _ => ll_bv n e
        end
    | EApp e1 e2 => VarSet.union (ll_bv n e1) (ll_bv n e2)
    | ELoc _ => VarSet.empty
    | ERef e => ll_bv n e
    | EDeref e => ll_bv n e
    | EAssign e1 e2 => VarSet.union (ll_bv n e1) (ll_bv n e2)
    | EBox e => ll_bv (S n) e
    | EUnbox e => ll_bv (pred n) e
    | ERun e => ll_bv n e
    | ELift e => ll_bv n e
    end.

  Lemma bv_ll_bv:
    forall (e:expr) (n:nat),
    depth e <= n ->
    bv n e = ll_bv n e.
  Proof.
    induction e ; simpl ; intros ;
    (* Const, Var, Loc *)
    try(reflexivity) ;
    (* App, Assign *)
    try(rewrite IHe1, IHe2 ; auto ;
    [apply max_lub_r in H | apply max_lub_l in H ];
    trivial ; fail) ;
    (* Ref, Deref, Run, Lift *)
    try(apply IHe ; auto ; fail).

    (* Abs *)
    destruct n ; simpl ;
    unfold BindingSet.bindSet, rho.
    rewrite <- beq_nat_refl.
    rewrite StageSetProperties.singleton_union_1.
    rewrite IHe ; auto.
    assert(beq_nat (S n) 0 = false).
    apply beq_nat_false_iff ; auto.
    rewrite H0.
    rewrite VarSetProperties.empty_union_1.
    apply IHe ; auto.

    (* Fix *)
    destruct n ; simpl ;
    unfold BindingSet.bindSet, rho.
    rewrite <- beq_nat_refl.
    repeat(rewrite StageSetProperties.singleton_union_1).
    rewrite IHe ; auto.
    assert(beq_nat (S n) 0 = false).
    apply beq_nat_false_iff ; auto.
    rewrite H0.
    repeat(rewrite VarSetProperties.empty_union_1).
    apply IHe ; auto.

    (* Box *)
    apply IHe ; auto.
    omega.

    (* Unbox *)
    destruct n ; simpl.
    inversion H.
    apply le_S_n in H.
    apply IHe ; assumption.
  Qed.

  Lemma bv_ll_bv_O:
    forall (e:expr) (n:nat),
    depth e = 0 ->
    bv 0 e = ll_bv 0 e.
  Proof.
    intros ; apply bv_ll_bv ; 
    auto ; omega.
  Qed.

End LispLikeCalculusProperties.
