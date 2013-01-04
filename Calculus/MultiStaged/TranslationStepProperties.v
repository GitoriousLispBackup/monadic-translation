Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.MinMax.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalChoice.
Require Import "Misc/Tactics".
Require Import "Misc/Library".
Require Import "Misc/Relation".
Require Import "Calculus/Sets".
Require Import "Calculus/Definitions".
Require Import "Calculus/Monad".
Require Import "Calculus/MultiStaged/Definitions".
Require Import "Calculus/MultiStaged/Properties".
Require Import "Calculus/MultiStaged/Monad".
Require Import "Calculus/MultiStaged/Translation".
Require Import "Calculus/MultiStaged/MonadStepProperties".
Require Import "Calculus/MultiStaged/TranslationStaticProperties".

Module ContextProperties (R:Replacement) (T:StagedCalculus) 
    (M:Monad R T) (MP:MonadStepProperties R T M).

  Module TranslationStaticProperties := TranslationStaticProperties R T M MP.
  Module StaticProperties := TranslationStaticProperties.ContextStaticProperties.
  Module Context := StaticProperties.Context.
  Import StaticProperties.
  Import MP.Translation.
  Import M.
  Import Context.

  Lemma fill_ssubst:
    forall (bs:list nat) (c:t) (n:nat) (ss:StageSet.t) (x:S.var) (v:S.expr) (e:T.expr),
    S.svalue 0 v -> VarSet.mem x (context_hole_set c) = false ->
      fill (ssubst_context n ss (hole_var x) c (phi v bs)) 
      (ssubst n ss (M.cast_var (hole_var x)) e (phi v bs)) = 
      ssubst n ss (cast_var (hole_var x)) (fill c e) (phi v bs).
    intros.
    induction c ; simpl.
    reflexivity.

    destruct a ; simpl in *|-*.
    assert(beq_nat (hole_var x) (hole_var v0) = false).
    assert(H1 := H0).
    apply VarSetProperties.add_mem_6 in H0.
    apply beq_nat_false_iff.
    unfold not ; intros ; unfold hole_var in *|-*.
    clear IHc H H1 ; omega.
    rewrite H1.
    rewrite IHc.
    rewrite MP.ssubst_bind with (f2 :=(fun v1 : T.expr =>
     cast_eapp
     (cast_eabs (cast_var (hole_var v0))
        (ssubst n ss (cast_var (hole_var x)) (fill c e) (phi v bs))) v1)).
    reflexivity.
    intros.
    rewrite MP.ssubst_eapp.
    rewrite MP.ssubst_eabs.
    assert(S.beq_var (hole_var x) (hole_var v0) = false).
    assumption.
    rewrite H2.
    reflexivity.
    apply VarSetProperties.add_mem_5 in H0.
    assumption.
  Qed.


End ContextProperties.

Module TranslationStepProperties (R:Replacement) 
    (T:StagedCalculus) (M:Monad R T) (MP:MonadStepProperties R T M). 

  Module Translation := MP.Translation.
  Module ContextProperties := ContextProperties R T M MP.
  Module StaticProperties := ContextProperties.TranslationStaticProperties.
  Module CalculusProperties := CalculusProperties R M.S.
  Module BindingSetProperties := BindingSetProperties R.
  Import StaticProperties.
  Import Translation.
  Import M.S.
  Import M.

  Lemma ssubst_fill_hole:
    forall (h:var) (e v:T.expr) (c:Context.t) (n:nat),
      VarSet.mem h (Context.context_hole_set c) = false ->
      ssubst n StageSet.empty (M.cast_var (hole_var h)) (Context.fill c e) v =
      Context.fill (Context.ssubst_context n StageSet.empty (hole_var h) c v) 
      (ssubst n StageSet.empty (M.cast_var (hole_var h)) e v).
  Proof.
    induction c ; intros ; simpl.
    reflexivity.
    destruct a.
    specialize (IHc n).
    simpl in H.
    assert(beq_nat (hole_var h) (hole_var v0) = false).
    apply VarSetProperties.add_mem_6 in H.
    apply beq_nat_false_iff.
    unfold not ; intros ; unfold hole_var in *|-*.
    clear IHc ; omega.
    rewrite H0.
    simpl.
    apply MP.ssubst_bind.
    intros.
    rewrite MP.ssubst_eapp.
    rewrite MP.ssubst_eabs.
    assert(beq_var (hole_var h) (hole_var v0) = false).
    assumption.
    rewrite H1.
    rewrite IHc.
    reflexivity.
    apply VarSetProperties.add_mem_5 in H.
    assumption.
  Qed.

  Lemma ssubst_fill_source:
    forall (x:var) (e v:T.expr) (c:Context.t) (ss:StageSet.t) (n:nat),
      ssubst n ss (M.cast_var (source_var x)) (Context.fill c e) v =
      Context.fill (Context.ssubst_context n ss (source_var x) c v) 
      (ssubst n ss (M.cast_var (source_var x)) e v).
  Proof.
    assert(forall (m n:nat), beq_nat (source_var m) (hole_var n) = false).
    intros ; unfold source_var, hole_var ; apply beq_nat_false_iff ; omega.
    induction c ; intros ; simpl.
    reflexivity.
    destruct a.
    specialize (IHc ss n).
    apply MP.ssubst_bind.
    intros.
    rewrite MP.ssubst_eapp.
    rewrite MP.ssubst_eabs.
    rewrite H ; rewrite H.
    rewrite IHc.
    reflexivity.
  Qed.

  Lemma ssubst_app_source:
    forall (x:var) (v:T.expr) (c1 c2:Context.t) (ss:StageSet.t) (n:nat),
      Context.ssubst_context n ss (source_var x) (c1++c2) v =
      (Context.ssubst_context n ss (source_var x) c1 v) ++
      (Context.ssubst_context n ss (source_var x) c2 v).
  Proof.
    assert(forall (m n:nat), beq_nat (source_var m) (hole_var n) = false).
    intros ; unfold source_var, hole_var ; apply beq_nat_false_iff ; omega.
    induction c1 ; intros ; simpl in *|-*.
    reflexivity.
    destruct a.
    rewrite H.
    rewrite IHc1.
    reflexivity.
  Qed.

  Lemma ssubst_merge_source:
    forall (x:var) (v:T.expr) (cs1 cs2:Context.t_stack) (ss:StageSet.t) (n:nat),
      Context.ssubst_stack n ss (source_var x) (Context.merge cs1 cs2) v =
      Context.merge (Context.ssubst_stack n ss (source_var x) cs1 v) 
      (Context.ssubst_stack n ss (source_var x) cs2 v).
  Proof.
    induction cs1 ; intros ; simpl in *|-*.
    reflexivity.
    destruct cs2 ; simpl.
    reflexivity.
    simpl.
    rewrite ssubst_app_source.
    rewrite IHcs1.
    reflexivity.
  Qed.

  Lemma trans_ssubst_source: 
    forall (e v:expr) (bs:list nat) (x:var) (ss:StageSet.t) (n:nat), 
    let (e', cs) := trans e bs in
    svalue 0 v ->
    depth v = 0 ->
    length cs <= n ->
    StageSet.ub n ss = true ->
    (trans (S.ssubst n ss x e v) bs =
    (M.ssubst n ss (cast_var (source_var x)) e' (phi v bs),
    Context.ssubst_stack (pred n) (StageSet.remove n ss) (source_var x) cs (phi v bs))
    /\ M.ssubst n ss (cast_var (source_var x)) (phi e bs) (phi v bs) =
      (phi (S.ssubst n ss x e v) bs)).
  Proof.
    assert(forall (x v:nat), beq_nat x v = 
    beq_nat (source_var x) (source_var v)) as HSInject.
    intros ; unfold source_var ; remember (beq_nat x v) ; 
    destruct b ; symmetry in Heqb ; symmetry.
    apply beq_nat_true_iff in Heqb.
    subst ; rewrite <- beq_nat_refl ; reflexivity.
    apply beq_nat_false_iff ; apply beq_nat_false in Heqb.
    omega.

    induction e ; simpl ; intros.

    (* Case EConst *)
    rewrite MP.ssubst_ret.
    rewrite MP.ssubst_econst.
    split ; intros ; reflexivity.
    
    (* Case EVar *)
    rewrite MP.ssubst_ret.
    rewrite MP.ssubst_evar.
    rewrite <- HSInject.
    destruct (beq_nat x v && CRaw.BindingSet.rho n ss).
    specialize (svalue_phi v0 bs H) ; intros.
    unfold trans_expr in H3.
    specialize (depth_length v0 bs) ; intros.
    rewrite H0 in H4.
    destruct (trans v0) ; subst.
    destruct t ; [|inversion H4].
    simpl in H4 ; split ; intros ; auto.
    split ; intros ; auto.
    
    (* EAbs *)
    specialize (IHe v0 bs x).
    destruct (trans e) ; intros.
    rewrite MP.ssubst_ret.
    rewrite MP.ssubst_eabs.
    rewrite <- HSInject.
    destruct (beq_nat x v).
    specialize (IHe (StageSet.add n ss) n H H0 H1).
    destruct IHe.
    rewrite <- StageSetProperties.ub_le_1 with (m:=n) ; auto.
    rewrite H3 ; auto.
    split ; intros ; auto.
    rewrite StageSetProperties.remove_add_remove ; auto.
    specialize (IHe ss n H H0 H1 H2).
    destruct IHe ; rewrite H3 ; auto.

    (* EFix *)
    specialize (IHe v1 bs x).
    destruct (trans e) ; intros.
    rewrite MP.ssubst_ret.
    rewrite MP.ssubst_efix.
    rewrite <- HSInject.
    rewrite <- HSInject.
    destruct (beq_nat x v || beq_nat x v0).
    specialize (IHe (StageSet.add n ss) n H H0 H1).
    destruct IHe.
    rewrite <- StageSetProperties.ub_le_1 with (m:=n) ; auto.
    rewrite H3 ; auto.
    split ; intros ; auto.
    rewrite StageSetProperties.remove_add_remove ; auto.
    specialize (IHe ss n H H0 H1 H2).
    destruct IHe ; rewrite H3 ; auto.

    (* EApp *)
    specialize (IHe1 v (map_iter_booker e2 bs 0) x).
    specialize (IHe2 v bs x).
    destruct (trans e1) ; destruct (trans e2) ; intros.
    specialize (IHe2 ss n H H0).
    specialize (IHe1 ss n H H0).
    destruct IHe2 ; auto.
    rewrite ContextStaticProperties.merge_length in H1.
    apply max_lub_iff in H1 ; destruct H1 ; assumption.
    destruct IHe1 ; auto.
    rewrite ContextStaticProperties.merge_length in H1.
    apply max_lub_iff in H1 ; destruct H1 ; assumption.
    rewrite H3 ; auto ; clear H3 H4.
    unfold map_iter_booker in *|-*.
    rewrite map_iter_ssubst ; auto.
    rewrite H5 ; auto.
    rewrite phi_depth_0 with (bs2:=nil) ; auto.
    assert(S.CRaw.svalueb 0 (S.ssubst n ss x e1 v) = S.CRaw.svalueb 0 e1) as Eq1.
    remember (CRaw.svalueb 0 e1) ; destruct b ; symmetry in Heqb.
    apply CalculusProperties.svalueb_iff ; 
    apply CalculusProperties.svalueb_iff in Heqb.
    apply CalculusProperties.svalue_ssubst ; auto.
    apply CalculusProperties.svalueb_iff_conv ; 
    apply CalculusProperties.svalueb_iff_conv in Heqb.
    unfold not ; intros.
    apply CalculusProperties.svalue_ssubst in H3 ; auto.
    rewrite Eq1 ; clear Eq1.
    rewrite ssubst_merge_source.
    rewrite <- H6.
    rewrite phi_depth_0 with (v:=v) (bs1:=(List2.map_iter 
      (fun b n0 => (b + booker e2 n0)%nat) bs 0)) (bs2:=nil) ; auto.
    destruct (CRaw.svalueb 0 e1).
    rewrite MP.ssubst_bind with (f2:=fun v2 => cast_eapp
      (ssubst n ss (cast_var (source_var x))
         (phi e1 (List2.map_iter (fun b n0 : nat => (b + booker e2 n0)%nat) bs 0))
         (phi v nil)) v2).
    split ; intros ; auto.
    rewrite MP.ssubst_econst ; auto.
    intros.
    rewrite MP.ssubst_eapp ; auto.
    rewrite MP.ssubst_bind with (f2:= fun v1 => bind 
      (ssubst n ss (cast_var (source_var x)) e0 (phi v nil))
      (fun v2 => cast_eapp v1 v2)).
    split ; intros ; auto.
    rewrite MP.ssubst_econst ; auto.
    intros.
    rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr =>
    cast_eapp (ssubst n ss (cast_var (source_var x)) v2 (phi v nil)) v0)).
    reflexivity.
    intros.
    rewrite MP.ssubst_eapp.
    reflexivity.

    (* ELoc *)
    rewrite MP.ssubst_ret, MP.ssubst_eloc ; split ; intros ; reflexivity.
    
    (* ERef *)
    specialize (IHe v bs x).
    destruct (trans e) ; intros.
    specialize (IHe ss n H H0 H1 H2).
    destruct IHe ; auto.
    rewrite H3 ; auto.
    rewrite MP.ssubst_bind with (f2:=fun v0 => cast_eref v0).
    split ; intros ; auto.
    rewrite MP.ssubst_econst ; auto.
    intros.
    rewrite MP.ssubst_eref.
    reflexivity.
    
    (* EDeref *)
    specialize (IHe v bs x).
    destruct (trans e) ; intros.
    specialize (IHe ss n H H0 H1 H2).
    destruct IHe ; auto.
    rewrite H3 ; auto.
    rewrite MP.ssubst_bind with (f2:=fun v0 => cast_ederef v0).
    split ; intros ; auto.
    rewrite MP.ssubst_econst ; auto.
    intros.
    rewrite MP.ssubst_ederef.
    reflexivity.

    (* EAssign *)
    specialize (IHe1 v (map_iter_booker e2 bs 0) x).
    specialize (IHe2 v bs x).
    destruct (trans e1) ; destruct (trans e2) ; intros.
    specialize (IHe2 ss n H H0).
    specialize (IHe1 ss n H H0).
    destruct IHe2 ; auto.
    rewrite ContextStaticProperties.merge_length in H1.
    apply max_lub_iff in H1 ; destruct H1 ; assumption.
    destruct IHe1 ; auto.
    rewrite ContextStaticProperties.merge_length in H1.
    apply max_lub_iff in H1 ; destruct H1 ; assumption.
    rewrite H3 ; auto ; clear H3 H4.
    unfold map_iter_booker in *|-*.
    rewrite map_iter_ssubst ; auto.
    rewrite H5 ; auto.
    rewrite phi_depth_0 with (bs2:=nil) ; auto.
    assert(S.CRaw.svalueb 0 (S.ssubst n ss x e1 v) = S.CRaw.svalueb 0 e1) as Eq1.
    remember (CRaw.svalueb 0 e1) ; destruct b ; symmetry in Heqb.
    apply CalculusProperties.svalueb_iff ; 
    apply CalculusProperties.svalueb_iff in Heqb.
    apply CalculusProperties.svalue_ssubst ; auto.
    apply CalculusProperties.svalueb_iff_conv ; 
    apply CalculusProperties.svalueb_iff_conv in Heqb.
    unfold not ; intros.
    apply CalculusProperties.svalue_ssubst in H3 ; auto.
    rewrite Eq1 ; clear Eq1.
    rewrite ssubst_merge_source.
    rewrite <- H6.
    rewrite phi_depth_0 with (v:=v) (bs1:=(List2.map_iter 
      (fun b n0 => (b + booker e2 n0)%nat) bs 0)) (bs2:=nil) ; auto.
    destruct (CRaw.svalueb 0 e1).
    rewrite MP.ssubst_bind with (f2:=fun v2 => cast_eassign
      (ssubst n ss (cast_var (source_var x))
         (phi e1 (List2.map_iter (fun b n0 : nat => (b + booker e2 n0)%nat) bs 0))
         (phi v nil)) v2).
    split ; intros ; auto.
    rewrite MP.ssubst_econst ; auto.
    intros.
    rewrite MP.ssubst_eassign ; auto.
    rewrite MP.ssubst_bind with (f2:= fun v1 => bind 
      (ssubst n ss (cast_var (source_var x)) e0 (phi v nil))
      (fun v2 => cast_eassign v1 v2)).
    split ; intros ; auto.
    rewrite MP.ssubst_econst ; auto.
    intros.
    rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr =>
    cast_eassign (ssubst n ss (cast_var (source_var x)) v2 (phi v nil)) v0)).
    reflexivity.
    intros.
    rewrite MP.ssubst_eassign.
    reflexivity.

    (* EBox *)
    specialize (IHe v (0::bs) x).
    destruct (trans e) ; intros.
    destruct t ; simpl in *|-* ; intros ;
    specialize (IHe ss (S n) H H0) ;
    destruct IHe.
    omega.
    apply StageSetProperties.ub_le_2 with (m:=n) ; auto.
    rewrite H3 ; auto ; simpl in *|-*.
    rewrite MP.ssubst_ret ; auto.
    rewrite MP.ssubst_ebox ; auto.
    rewrite phi_depth_0 with (bs2:=bs) ; auto.
    omega.
    apply StageSetProperties.ub_le_2 with (m:=n) ; auto.
    rewrite ssubst_fill_source.
    rewrite phi_depth_0 with (bs1:=0::bs) (bs2:=bs) in H3 ; auto.
    rewrite MP.ssubst_ret ; auto.
    rewrite MP.ssubst_ebox ; auto.
    assert(StageSet.remove (S n) ss = ss).
    apply StageSetProperties.remove_equal.
    remember(Sets.NatSet.MSetIntern.mem (S n) ss).
    destruct b ; symmetry in Heqb.
    exfalso ; apply StageSetProperties.ub_le_3 with (n:=n) in Heqb ; 
    [omega|auto].
    reflexivity.
    rewrite H3 ; auto ; simpl in *|-*.
    rewrite H5.
    split ; intros ; auto.

    (* EUnbox *)
    destruct (List2.hd_cons bs 0).
    specialize (IHe v l x).
    destruct (trans e) ; intros.
    specialize (IHe (StageSet.remove n ss) (pred n) H H0).
    destruct IHe ; auto.
    simpl in H1 ; destruct n ; omega.
    rewrite <- StageSetProperties.ub_pred ; auto.
    rewrite H3 ; auto.
    rewrite MP.ssubst_eunbox ; auto.
    simpl.
    rewrite MP.ssubst_evar.
    assert(beq_nat (source_var x) (hole_var n0) &&
       CRaw.BindingSet.rho (pred n) (StageSet.remove n ss) = false).
    apply andb_false_iff ; left.
    apply beq_nat_false_iff.
    unfold source_var, hole_var ; omega.
    rewrite H5 ; clear H5.
    rewrite phi_depth_0 with (bs2:=bs) ; auto.
    split ; intros ; auto.
    rewrite MP.ssubst_econst ; auto. 

    (* ERun *)
    specialize (IHe v bs x).
    destruct (trans e) ; intros.
    specialize (IHe ss n H H0 H1 H2).
    destruct IHe ; auto.
    rewrite H3 ; auto.
    rewrite MP.ssubst_bind with (f2:=fun v0 => cast_erun v0).
    split ; intros ; auto.
    rewrite MP.ssubst_econst ; auto.
    intros.
    rewrite MP.ssubst_erun.
    reflexivity.

    (* ELift *)
    specialize (IHe v bs x).
    destruct (trans e) ; intros.
    specialize (IHe ss n H H0 H1 H2).
    destruct IHe ; auto.
    rewrite H3 ; auto.
    rewrite MP.ssubst_bind with (f2:=fun v0 => cast_elift v0).
    split ; intros ; auto.
    rewrite MP.ssubst_econst ; auto.
    intros.
    rewrite MP.ssubst_elift.
    reflexivity.
  Qed.

  Lemma context_mem_length_booker:
    forall (e:S.expr) (bs:list nat),
    let (_, cs) := trans e bs in
    forall (n:nat),
    length (nth n cs nil) = booker e n.
  Proof.
    induction e ; simpl ; intros ; 
    try(destruct n ; auto ; fail) ;

    try(specialize(IHe bs) ;
    destruct (trans e) ; intros ;
    apply IHe ; fail) ;

    try(specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ;
    destruct (trans e1) ; destruct (trans e2) ; intros ;
    rewrite ContextStaticProperties.merge_nth ;
    rewrite app_length ;
    rewrite IHe1, IHe2 ; reflexivity).

    specialize (IHe (0::bs)).
    destruct (trans e).
    destruct t ; intros ; simpl in *|-*.
    specialize (IHe (S n)) ; destruct n ; auto.
    specialize (IHe (S n)) ; simpl in *|-*.
    assumption.
    
    destruct (List2.hd_cons bs 0).
    specialize (IHe l).
    destruct (trans e) ; intros.
    simpl in *|-*.
    destruct n0 ; auto.
  Qed.

  Lemma context_mem_booker:
    forall (e:S.expr) (bs:list nat),
    let (_, cs) := trans e bs in
    forall (n:nat) (v:var),
    n < length bs ->
    VarSet.mem v (Context.context_hole_set (nth n cs nil)) = true ->
    nth n bs 0 <= v < (nth n bs 0) + (booker e n).
  Proof.
    induction e ; simpl ; intros ;
    
    try(destruct n ; inversion H0 ; fail) ;

    try(specialize (IHe bs) ;
    destruct (trans e) ; intros ;
    apply IHe ; auto ; fail) ;

    try(specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ; unfold map_iter_booker in *|-* ;
    destruct (trans e1) ; destruct (trans e2) ; intros ;
    rewrite ContextStaticProperties.merge_nth in H0 ;
    rewrite ContextStaticProperties.context_hole_set_app in H0 ;
    rewrite VarSetProperties.union_mem in H0 ;
    apply orb_true_iff in H0 ; destruct H0 ; [
    rewrite List2Properties.length_map_iter in IHe1 ;
    specialize (IHe1 n v H H0) ; clear IHe2 ;
    specialize(List2Properties.map_iter_nth_indep
    (fun b n => (b + booker e2 n)%nat) bs n 0 0 0 H) ; intros ;
    rewrite H1 in IHe1 ;
    destruct IHe1 ; split ; rewrite plus_0_r in H3 ; omega|
    clear IHe1 ; specialize (IHe2 n v H H0) ; omega]).

    specialize (IHe (0::bs)).
    destruct (trans e).
    destruct t ; simpl in *|-* ; intros.
    destruct n ; simpl in H0 ; inversion H0.
    apply lt_n_S in H.
    specialize (IHe (S n) v H H0) ; clear H H0 ; simpl in *|-*.
    assumption.
    
    destruct bs ; simpl in *|-*.
    specialize (IHe nil).
    destruct (trans e) ; intros.
    destruct n ; simpl in *|-*.
    rewrite <- VarSetProperties.singleton_equal_add in H0.
    rewrite VarSetProperties.singleton_mem in H0.
    subst ; omega.
    apply lt_S in H ; apply lt_S_n in H.
    specialize (IHe n v H H0) ; clear H H0.
    destruct n ; omega.

    specialize (IHe bs).
    destruct (trans e) ; intros ; simpl in *|-*.
    destruct n0 ; simpl in *|-*.
    rewrite <- VarSetProperties.singleton_equal_add in H0.
    rewrite VarSetProperties.singleton_mem in H0.
    subst ; omega.
    apply IHe ; auto.
    apply lt_S_n in H ; auto.
  Qed.
    
  Lemma context_mem:
    forall (e:S.expr) (bs:list nat),
    let (_, cs) := trans e bs in
    forall (n:nat),
    n < length bs ->
    match nth n cs nil with
    | nil => True
    | (e, v) :: c => VarSet.mem v (Context.context_hole_set c) = false
    end.
  Proof.
    induction e ; intros ; simpl in *|-* ; intros ;
    try(destruct n ; auto ; fail) ;

    try(specialize (IHe bs) ;
    destruct (trans e bs) ; intros ;
    specialize (IHe n H) ;
    assumption).

    (* EApp *)
    specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ;
    specialize (context_mem_booker e1 (map_iter_booker e2 bs 0)) ; 
    intros CMB1 ;
    specialize (context_mem_booker e2 bs) ; intros CMB2 ;
    destruct (trans e1) ; destruct (trans e2) ;
    intros ; specialize (IHe1 n) ; specialize (IHe2 n) ;
    rewrite ContextStaticProperties.merge_nth ;
    specialize (CMB1 n) ; specialize (CMB2 n) ;
    destruct (nth n t nil) ; simpl ; [
    apply IHe2 ; auto |].
    destruct p ;
    rewrite ContextStaticProperties.context_hole_set_app ;
    rewrite VarSetProperties.union_mem ;
    apply orb_false_iff ; 
    unfold map_iter_booker in *|-* ; split.
    rewrite List2Properties.length_map_iter in IHe1.
    apply IHe1 ; auto.
    rewrite List2Properties.length_map_iter in CMB1.
    remember (VarSet.mem v (Context.context_hole_set (nth n t0 nil))).
    symmetry in Heqb ; destruct b ; auto ; exfalso.
    apply CMB2 in Heqb ; auto ; clear CMB2.
    assert(VarSet.mem v (Context.context_hole_set ((e3, v) :: t1)) = true).
    simpl ; apply VarSetProperties.add_mem_3.
    specialize (CMB1 v H H0) ; clear H0 IHe2 IHe1 ;
    specialize(List2Properties.map_iter_nth_indep 
      (fun b n => (b + booker e2 n)%nat) bs n 0 0 0 H) ; intros ;
    rewrite plus_0_r in H0 ; rewrite H0 in CMB1 ; clear H0 ;
    omega.

    (* EAssign (same as EApp. Should deduplicate) *)
    specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ;
    specialize (context_mem_booker e1 (map_iter_booker e2 bs 0)) ; 
    intros CMB1 ;
    specialize (context_mem_booker e2 bs) ; intros CMB2 ;
    destruct (trans e1) ; destruct (trans e2) ;
    intros ; specialize (IHe1 n) ; specialize (IHe2 n) ;
    rewrite ContextStaticProperties.merge_nth ;
    specialize (CMB1 n) ; specialize (CMB2 n) ;
    destruct (nth n t nil) ; simpl ; [
    apply IHe2 ; auto |].
    destruct p ;
    rewrite ContextStaticProperties.context_hole_set_app ;
    rewrite VarSetProperties.union_mem ;
    apply orb_false_iff ; unfold map_iter_booker in *|-* ; split.
    rewrite List2Properties.length_map_iter in IHe1.
    apply IHe1 ; auto.
    rewrite List2Properties.length_map_iter in CMB1.
    remember (VarSet.mem v (Context.context_hole_set (nth n t0 nil))).
    symmetry in Heqb ; destruct b ; auto ; exfalso.
    apply CMB2 in Heqb ; auto ; clear CMB2.
    assert(VarSet.mem v (Context.context_hole_set ((e3, v) :: t1)) = true).
    simpl ; apply VarSetProperties.add_mem_3.
    specialize (CMB1 v H H0) ; clear H0 IHe2 IHe1 ;
    specialize(List2Properties.map_iter_nth_indep 
      (fun b n => (b + booker e2 n)%nat) bs n 0 0 0 H) ; intros ;
    rewrite plus_0_r in H0 ; rewrite H0 in CMB1 ; clear H0 ;
    omega.
    
    specialize (IHe (0 :: bs)).
    destruct (trans e) ; intros.
    destruct t ; simpl in *|-* ; intros.
    destruct n ; auto.
    specialize (IHe (S n)).
    apply IHe ; auto.
    apply lt_n_S ; auto.

    destruct bs ; simpl in *|-*.
    specialize (IHe nil).
    destruct (trans e nil) ; intros.
    simpl in *|-*.
    destruct n ; auto.
    apply IHe ; auto ; omega.

    specialize (IHe bs).
    destruct (trans e) ; intros.
    simpl in *|-*.
    destruct n0 ; auto.
    apply IHe ; auto.
    omega.
  Qed.

  Lemma trans_mem_length:
    forall (M:Memory.t) (bs:list nat), 
    length (trans_mem M bs) = length M.
  Proof.
    induction M ; simpl ; intros ; auto.
  Qed.

  Lemma trans_mem_fresh:
    forall (M:Memory.t) (bs:list nat), 
    T.Memory.fresh (trans_mem M bs) = Memory.fresh M.
  Proof.
    induction M ; simpl ; intros ; auto.
  Qed.

  Lemma trans_mem_set:
    forall (M:Memory.t) (l:CRaw.location) (bs:list nat) (v:S.expr),
    l <= length M ->
    trans_mem (CRaw.Memory.set l v M) bs =
    T.Memory.set l (phi v bs) (trans_mem M bs).
  Proof.
    induction M ; simpl ; intros.
    apply le_n_0_eq in H ; subst ; auto.
    destruct l ; simpl ; auto.
    apply le_S_n in H.
    rewrite IHM ; auto.
  Qed.

  Lemma trans_mem_get:
    forall (M:Memory.t) (l:CRaw.location) (bs:list nat),
    l < length M ->
    phi (CRaw.Memory.get l M) bs =
    T.Memory.get l (trans_mem M bs).
  Proof.
    induction M ; simpl ; intros.
    apply lt_n_O in H ; contradiction.
    destruct l ; simpl ; auto.
    apply lt_S_n in H.
    unfold CRaw.Memory.get, T.Memory.get ; simpl.
    specialize (IHM l bs H).
    unfold CRaw.Memory.get, T.Memory.get in IHM ; simpl in IHM.
    rewrite IHM ; auto.
  Qed.

  Inductive congr_context_ssubst 
    (P:nat -> CRaw.var -> nat -> T.expr -> nat -> T.expr -> T.expr -> Prop) 
    (n:nat) (h:CRaw.var)
    (m:nat) (v:T.expr) (b1 b2:nat) : Context.t -> Context.t -> Prop :=
  | CongrCSubst_nil : congr_context_ssubst P n h m v b1 b2 nil nil
  | CongrCSubst_cons : forall (u1 u2:T.expr) (c1 c2:Context.t),
      P n h m v b1 u1 u2 ->
      congr_context_ssubst P n h m v b1 b2 c1 c2 ->
      congr_context_ssubst P n h m v b1 b2
        (cons (u1,(b2+(length c1))%nat) c1) 
        (cons (u2,(b2+(length c1))%nat) c2).

  Inductive congr_stack_ssubst 
    (P:nat -> CRaw.var -> nat -> T.expr -> nat -> T.expr -> T.expr -> Prop) 
    (n:nat) (h:CRaw.var) (v:T.expr) : 
    list nat -> nat -> Context.t_stack -> Context.t_stack -> Prop :=
  | CongrSSubst_nil : forall (bs:list nat) (b:nat), congr_stack_ssubst P n h v bs b nil nil
  | CongrSSubst_cons_nil: forall (c1 c2:Context.t) (bs:list nat) (b1 b2:nat),
      congr_context_ssubst P n h 0 v b1 b2 c1 c2 ->
      congr_stack_ssubst P n h v (b1::bs) b2 (c1::nil) (c2::nil)
  | CongrSSubst_cons : forall (bs:list nat) (b1 b2:nat) (c1 c2 c1' c2':Context.t) (cs1 cs2:Context.t_stack),
      congr_context_ssubst P n h (length c1') v b1 b2 c1 c2 ->
      congr_stack_ssubst P (pred n) h v bs b1 (c1'::cs1) (c2'::cs2) ->
      congr_stack_ssubst P n h v (b1::bs) b2 (c1::c1'::cs1) (c2::c2'::cs2).

  Lemma congr_ssubst_context_app:
    forall (P:nat -> CRaw.var -> nat -> T.expr -> nat -> T.expr -> T.expr -> Prop)
    (c1 c2 c3 c4:Context.t) (n m b1 b2:nat) (h:S.var) (v:T.expr),
    congr_context_ssubst P n h m v b1 (b2 + length c2) c1 c3 ->
    congr_context_ssubst P n h m v b1 b2 c2 c4 ->
    congr_context_ssubst P n h m v b1 b2 (c1 ++ c2) (c3 ++ c4).
  Proof.
    induction c1 ; simpl ; intros ;
    inversion H ; subst ; auto.
    assert((b2 + length c2 + length c1) = b2 + (length (c1++c2)))%nat as Eq1.
    rewrite app_length ; simpl ; omega.
    rewrite Eq1 ; constructor ; auto.
  Qed.

  Definition ltb (m n:nat) := leb (S m) n.

  Definition admin_ssubst (n:nat) (h:CRaw.var) 
      (m:nat) (v:T.expr) (b:nat) (u1 u2:T.expr) : Prop :=
      forall (ss:StageSet.t), StageSet.mem 0 ss = false ->
      StageSet.ub n ss = true ->
      admin
        (M.ssubst n (match n with
	  | S (S n) => if ltb h (b + m) 
       		then StageSet.add (S n) ss else ss
	  | _ => ss
          end) (M.cast_var (hole_var h)) u1 v) u2.

  Definition admin_context_ssubst := congr_context_ssubst admin_ssubst.
  Definition admin_stack_ssubst := congr_stack_ssubst admin_ssubst.

  Lemma admin_fill_ssubst_1:
    forall (e:S.expr) (bs:list nat),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) in
    match cs with
    | c1 :: nil => 
      match c1 with
      | nil => False
      | (eh, h) :: c1' => let b := hd 0 bs in
        forall (v e2:T.expr) (c2:Context.t),
        admin_context_ssubst 0 h 0 v b 0 c1' c2 ->
        admin_ssubst 1 h (booker e 0) v 0 e1 e2 ->
        admin_ssubst 0 h (booker e 1) v b
        (Context.fill c1' (ret (cast_ebox e1))) (Context.fill c2 (ret (cast_ebox e2)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (context_stack_not_nil e (0::bs)) ; intros CSNotNil.
    specialize (length_h_match e (0::bs)) ; intros LengthHMatch.
    destruct (trans e (0 :: bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t ; auto.
    exfalso ; apply CSNotNil ; simpl ; auto.
    
    simpl in *|-*.
    assert (1 <= S (length bs)) as Tmp1.
    clear ; omega.
    specialize (LengthHMatch Tmp1).
    simpl in *|-* ; clear Tmp1.
    assert(let (_, h) := p in h >= length t) as Tmp3.
    destruct p ; omega.
    clear LengthHMatch.
    induction t ; simpl ; intros.
    destruct p ; subst ; intros.
    unfold admin_ssubst ; intros.
    inversion H0 ; subst ; simpl.
    rewrite MP.ssubst_ret, MP.ssubst_ebox ; auto.
    repeat(constructor).
    apply H1 ; auto.
    simpl in *|-*.
    rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto.
    destruct p ; subst ; intros.
    assert(Tmp4 := Tmp3).
    apply lt_le_weak in Tmp3.
    inversion H0 ; subst ; simpl.
    unfold admin_ssubst ; intros.
    simpl in *|-*.
    assert(~ ((e1, v) :: t = nil \/ False)) as Tmp2.
    unfold not ; clear ; intros ; destruct H ; auto ; inversion H.
    specialize (IHt Tmp2 Tmp3 v0 e2 c0 H6 H1).

    assert(beq_var (hole_var v) (hole_var (length t)) = false) as BeqFalse1.
    subst ; unfold hole_var ; apply beq_nat_false_iff ; 
    generalize Tmp4 ; clear ; intros ; omega.

    rewrite MP.ssubst_bind with (f2:= fun v2 =>
        (cast_eapp (cast_eabs (cast_var (hole_var (length t)))
         (ssubst 0 ss (cast_var (hole_var v)) 
           (Context.fill t (ret (cast_ebox e0))) v0)) v2)); auto.
    constructor ; auto ; intros.
    constructor ; [| constructor].
    constructor.
    apply IHt ; auto ; intros.
    intros.
    rewrite MP.ssubst_eapp, MP.ssubst_eabs, BeqFalse1 ; auto.
  Qed.

  Lemma admin_fill_ssubst_2_strong:
    forall (e:S.expr) (bs:list nat),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) in
    match cs with
    | c1 :: c1' :: nil => 
      match c1' with
      | nil => False
      | (eh, h) :: c1'' => let b := hd 0 bs in
        forall (v e2:T.expr) (c2:Context.t) (ss:StageSet.t),
        StageSet.mem 0 ss = false ->
        StageSet.ub 1 ss = true ->
        admin_context_ssubst 1 h (length c1'') v b 0 c1 c2 ->
        admin (M.ssubst 2 (if ltb h (booker e 0) then StageSet.add 1 ss else ss)
	  (M.cast_var (hole_var h)) e1 v) e2 ->
        admin (M.ssubst 1 ss (M.cast_var (hole_var h)) 
          (Context.fill c1 (ret (cast_ebox e1))) v) 
          (Context.fill c2 (ret (cast_ebox e2)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (depth_length e (0::bs)) ; intros DpthLength1.
    specialize (context_stack_not_nil e (0::bs)) ; intros CSNotNil.
    specialize (length_h_match e (0::bs)) ; intros LengthHMatch.
    specialize (booker_length e (0::bs)) ; intros BookerLength.
    destruct (trans e (0 :: bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t1 ; auto.
    destruct t0 ; auto.
    exfalso ; apply CSNotNil ; simpl ; auto.

    rewrite BookerLength ; simpl.
    clear LengthHMatch BookerLength CSNotNil.
    induction t.
    destruct p ; intros.
    inversion H2 ; subst ; simpl in *|-*.
    rewrite MP.ssubst_ret, MP.ssubst_ebox ; repeat(constructor) ; auto.

    simpl in *|-*.
    destruct p ; intros.
    inversion H2 ; subst ; simpl in *|-*.
    rewrite DpthLength1 in H ; destruct bs.
    exfalso ; generalize H ; clear ; simpl ; intros ; omega.
    specialize (IHt DpthLength1 v0 e2 c0) ; simpl in *|-*.
    case_beq_nat v (length t).
      rewrite MP.ssubst_bind with (f2:= fun v2 =>
        (cast_eapp (cast_eabs (cast_var (hole_var (length t)))
         (ssubst 1 (StageSet.add 1 ss) (cast_var (hole_var (length t))) 
           (Context.fill t (ret (cast_ebox e0))) v0)) v2)); auto.
      constructor ; auto ; intros.
      repeat(constructor).
      apply IHt ; auto.
      rewrite StageSetProperties.add_mem_4 ; auto.
      rewrite <- StageSetProperties.ub_le_1 ; auto.
      assert(ltb (length t) (S (length t)) = true).
      clear ; unfold ltb ; apply leb_iff ; omega.
      rewrite H4 in H3 ; clear H4.
      assert(ltb (length t) (length t) = false).
      clear ; unfold ltb ; apply leb_iff_conv ; omega.
      rewrite H4 ; clear H4 ; auto.
      intros.
      rewrite MP.ssubst_eapp, MP.ssubst_eabs ; auto.
      rewrite <- beq_nat_refl ; auto.

      assert(ltb v (length t) = ltb v (S (length t))) as LtbEq.
      generalize E ; clear ; intros ; unfold ltb.
      remember (leb (S v) (S (length t))).
      destruct b ; symmetry in Heqb.
      apply leb_iff ; apply leb_iff in Heqb ; omega.
      apply leb_iff_conv ; apply leb_iff_conv in Heqb ; omega.
      rewrite LtbEq in IHt ; clear LtbEq.

      rewrite MP.ssubst_bind with (f2:= fun v2 =>
        (cast_eapp (cast_eabs (cast_var (hole_var (length t)))
         (ssubst 1 ss (cast_var (hole_var v)) 
           (Context.fill t (ret (cast_ebox e0))) v0)) v2)); auto.
      constructor ; auto ; intros.
      repeat(constructor).
      apply IHt ; auto.
      intros.
      rewrite MP.ssubst_eapp, MP.ssubst_eabs ; auto.
      assert(beq_var (hole_var v) (hole_var (length t)) = false).
      generalize E ; clear ; intros ; unfold hole_var ; 
      apply beq_nat_false_iff ; omega.
      rewrite H4 ; auto.
  Qed.

  Lemma admin_fill_ssubst_2:
    forall (e:S.expr) (bs:list nat),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) in
    match cs with
    | c1 :: c1' :: nil => 
      match c1' with
      | nil => False
      | (eh, h) :: c1'' => let b := hd 0 bs in
        forall (v e2:T.expr) (c2:Context.t),
        admin_context_ssubst (pred (depth e)) h (length c1'') v b 0 c1 c2 ->
        admin_ssubst (depth e) h (booker e 0) v 0 e1 e2 ->
        admin_ssubst (pred (depth e)) h (booker e 1) v b
        (Context.fill c1 (ret (cast_ebox e1))) (Context.fill c2 (ret (cast_ebox e2)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (admin_fill_ssubst_2_strong e bs H) ; intros Strong.
    specialize (depth_length e (0::bs)) ; intros DpthLength1.
    specialize (booker_length e (0::bs)) ; intros BookerLength.
    destruct (trans e (0 :: bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t1 ; auto.
    destruct t0 ; auto.
    destruct p ; intros ; auto.
    rewrite DpthLength1 in *|-* ; simpl in *|-* ; auto.
    rewrite BookerLength in *|-* ; simpl in *|-* ; auto.
    unfold admin_ssubst ; simpl ; intros.
    apply Strong ; auto.
    apply H1 ; auto.
    rewrite StageSetProperties.ub_le_2 with (m:=1) ; auto.
  Qed.

  Lemma admin_fill_ssubst_3_strong:
    forall (e:S.expr) (bs:list nat),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) in
    match cs with
    | _ :: _ :: nil => True
    | c1 :: c1' :: cs => 
	let (ch, _) := Context.shift (c1 :: c1' :: cs) in
	match ch with
	| nil => False
	| (eh, h) :: _ => let b := hd 0 bs in
          forall (v e2:T.expr) (c2:Context.t) (ss:StageSet.t),
          StageSet.mem 0 ss = false ->
          StageSet.ub (pred (depth e)) ss = true ->
          admin_context_ssubst (pred (depth e)) h (length c1') v b 0 c1 c2 ->
          admin (M.ssubst (depth e) (if ltb h (0 + (booker e 0)) 
       		then StageSet.add (pred (depth e)) 
                (if ltb h (b + (booker e 1)) 
       		then StageSet.add (pred (pred (depth e))) ss else ss)
                else (if ltb h (b + (booker e 1)) 
       		then StageSet.add (pred (pred (depth e))) ss else ss))
        	  (M.cast_var (hole_var h)) e1 v) e2 ->
          admin (M.ssubst (pred (depth e)) (if ltb h (b + (booker e 1)) 
       		then StageSet.add (pred (pred (depth e))) ss else ss)
          	  (M.cast_var (hole_var h)) 
            (Context.fill c1 (ret (cast_ebox e1))) v) 
            (Context.fill c2 (ret (cast_ebox e2)))
	end
    | _ => True
    end.
  Proof.
    intros.
    specialize (depth_length e (0::bs)) ; intros DpthLength1.
    specialize (context_stack_not_nil e (0::bs)) ; intros CSNotNil.
    specialize (length_h_match e (0::bs)) ; intros LengthHMatch.
    specialize (booker_length e (0::bs)) ; intros BookerLength.
    destruct (trans e (0 :: bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t1 ; auto.
    specialize (context_shift_not_nil (t :: t0 :: t1 :: t2)) ; intros CShiftNotNil.
    destruct (Context.shift).
    destruct t3 ; auto.
    assert(length (t :: t0 :: t1 :: t2) > 0).
    simpl ; omega.
    specialize (CShiftNotNil H0 CSNotNil) ; destruct CShiftNotNil.
    apply H1 ; auto.

    rewrite BookerLength ; rewrite BookerLength ; simpl.
    clear LengthHMatch BookerLength CShiftNotNil CSNotNil.
    induction t.
    destruct p ; intros.
    inversion H2 ; subst ; rewrite DpthLength1 in *|-* ; simpl in *|-*.
    rewrite MP.ssubst_ret, MP.ssubst_ebox ; repeat(constructor) ; auto.

    simpl in *|-*.
    destruct p ; intros.
    inversion H2 ; subst ; simpl in *|-*.
    rewrite DpthLength1 in H ; destruct bs.
    exfalso ; generalize H ; clear ; simpl ; intros ; omega.
    destruct bs.
    exfalso ; generalize H ; clear ; simpl ; intros ; omega.
    specialize (IHt DpthLength1 v0 e2 c0) ; simpl in *|-*.
    rewrite DpthLength1 in *|-* ; simpl in *|-*.

    case_beq_nat v (length t).
      assert((if ltb (length t) (n + length t0) 
         then StageSet.add (S (length t2)) (StageSet.add (S (S (length t2))) ss) 
         else (StageSet.add (S (S (length t2))) ss)) =
         (StageSet.add (S (S (length t2))) (if ltb (length t) (n + length t0) 
         then StageSet.add (S (length t2)) ss 
         else ss))) as Eq1.
         destruct (ltb (length t) (n + length t0)) ; auto.
         apply StageSetProperties.add_add.
      rewrite MP.ssubst_bind with (f2:= fun v2 =>
        (cast_eapp (cast_eabs (cast_var (hole_var (length t)))
         (ssubst (S (S (length t2)))
         (if ltb (length t) (n + length t0) 
         then StageSet.add (S (length t2)) (StageSet.add (S (S (length t2))) ss) 
         else (StageSet.add (S (S (length t2))) ss))
           (cast_var (hole_var (length t))) 
           (Context.fill t (ret (cast_ebox e0))) v0)) v2)); auto.
      constructor ; auto ; intros.
      repeat(constructor).
      apply IHt ; auto.
      rewrite StageSetProperties.add_mem_4 ; auto.
      rewrite <- StageSetProperties.ub_le_1 ; auto.
      assert(ltb (length t) (S (length t)) = true).
      clear ; unfold ltb ; apply leb_iff ; omega.
      rewrite H4 in H3 ; clear H4.
      assert(ltb (length t) (length t) = false).
      clear ; unfold ltb ; apply leb_iff_conv ; omega.
      rewrite H4 ; clear H4 ; auto.
      rewrite <- Eq1 in H3 ; auto.
      intros.
      rewrite MP.ssubst_eapp, MP.ssubst_eabs ; auto.
      rewrite <- beq_nat_refl ; auto.
      destruct (ltb (length t) (n + length t0)) ;
      auto ; rewrite Eq1 ; auto.

      assert(ltb v (length t) = ltb v (S (length t))) as LtbEq.
      generalize E ; clear ; intros ; unfold ltb.
      remember (leb (S v) (S (length t))).
      destruct b ; symmetry in Heqb.
      apply leb_iff ; apply leb_iff in Heqb ; omega.
      apply leb_iff_conv ; apply leb_iff_conv in Heqb ; omega.
      rewrite LtbEq in IHt ; clear LtbEq.

      rewrite MP.ssubst_bind with (f2:= fun v2 =>
        (cast_eapp (cast_eabs (cast_var (hole_var (length t)))
          (ssubst (S (S (length t2))) 
          (if ltb v (n + length t0) then StageSet.add (S (length t2)) ss else ss)
          (cast_var (hole_var v)) 
           (Context.fill t (ret (cast_ebox e0))) v0)) v2)); auto.
      constructor ; auto ; intros.
      repeat(constructor).
      apply IHt ; auto.
      intros.
      rewrite MP.ssubst_eapp, MP.ssubst_eabs ; auto.
      assert(beq_var (hole_var v) (hole_var (length t)) = false).
      generalize E ; clear ; intros ; unfold hole_var ; 
      apply beq_nat_false_iff ; omega.
      rewrite H4 ; auto.
  Qed.

  Lemma admin_fill_ssubst_3:
    forall (e:S.expr) (bs:list nat),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) in
    match cs with
    | _ :: _ :: nil => True
    | c1 :: c1' :: cs => 
	let (ch, _) := Context.shift (c1 :: c1' :: cs) in
	match ch with
	| nil => False
	| (eh, h) :: _ => let b := hd 0 bs in
          forall (v e2:T.expr) (c2:Context.t),
          admin_context_ssubst (pred (depth e)) h (length c1') v b 0 c1 c2 ->
          admin_ssubst (depth e) h (booker e 0) v 0 e1 e2 ->
          admin_ssubst (pred (depth e)) h (booker e 1) v b
          (Context.fill c1 (ret (cast_ebox e1))) (Context.fill c2 (ret (cast_ebox e2)))
	end
    | _ => True
    end.
  Proof.
    intros.
    specialize (depth_length e (0::bs)) ; intros DpthLength1.
    specialize (admin_fill_ssubst_3_strong e bs H) ; intros Strong.
    destruct (trans e (0 :: bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t1 ; auto.
    destruct (Context.shift).
    destruct t3 ; auto.
    destruct p ; intros ; auto.
    rewrite DpthLength1 in *|-* ; simpl in *|-* ; auto.
    unfold admin_ssubst ; simpl ; intros.
    apply Strong ; auto.
    unfold admin_ssubst in H1 ; simpl in H1.
    apply H1 ; auto.
    destruct (ltb v (hd 0 bs + booker e 1)) ; auto.
    rewrite StageSetProperties.add_mem_4 ; auto.
    destruct (ltb v (hd 0 bs + booker e 1)) ; [
    rewrite <- StageSetProperties.ub_le_1 ; auto |] ;
    rewrite StageSetProperties.ub_le_2 with (m:=S (S (length t2))) ; auto.
  Qed.

  Lemma admin_fill_ssubst:
    forall (e:S.expr) (bs:list nat),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) in
    match cs with
    | nil => True
    | c1 :: nil => 
      match c1 with
      | nil => False
      | (eh, h) :: c1' => let b := hd 0 bs in
        forall (v e2:T.expr) (c2:Context.t),
        admin_context_ssubst 0 h 0 v b 0 c1' c2 ->
        admin_ssubst 1 h (booker e 0) v 0 e1 e2 ->
        admin_ssubst 0 h (booker e 1) v b
        (Context.fill c1' (ret (cast_ebox e1))) (Context.fill c2 (ret (cast_ebox e2)))
      end
    | c1 :: c1' :: nil => 
      match c1' with
      | nil => False
      | (eh, h) :: c1'' => let b := hd 0 bs in
        forall (v e2:T.expr) (c2:Context.t),
        admin_context_ssubst (pred (depth e)) h (length c1'') v b 0 c1 c2 ->
        admin_ssubst (depth e) h (booker e 0) v 0 e1 e2 ->
        admin_ssubst (pred (depth e)) h (booker e 1) v b
        (Context.fill c1 (ret (cast_ebox e1))) (Context.fill c2 (ret (cast_ebox e2)))
      end
    | c1 :: c1' :: cs => 
	let (ch, _) := Context.shift (c1 :: c1' :: cs) in
	match ch with
	| nil => False
	| (eh, h) :: _ => let b := hd 0 bs in
          forall (v e2:T.expr) (c2:Context.t),
          admin_context_ssubst (pred (depth e)) h (length c1') v b 0 c1 c2 ->
          admin_ssubst (depth e) h (booker e 0) v 0 e1 e2 ->
          admin_ssubst (pred (depth e)) h (booker e 1) v b
          (Context.fill c1 (ret (cast_ebox e1))) (Context.fill c2 (ret (cast_ebox e2)))
	end
    end.
  Proof.
    intros.
    specialize (admin_fill_ssubst_1 e bs) ; intros Case1.
    specialize (admin_fill_ssubst_2 e bs) ; intros Case2.
    specialize (admin_fill_ssubst_3 e bs) ; intros Case3.
    destruct (trans e (0 :: bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t ; auto.
    destruct p ; intros ; auto.
    destruct t1 ; auto.
    destruct t0 ; auto.
    destruct p ; intros ; auto.
    destruct (Context.shift) ; auto.
    destruct t3 ; auto.
    destruct p ; intros ; auto.
  Qed.

  Definition eq_ssubst (n:nat) (h:CRaw.var) 
      (m:nat) (v:T.expr) (b:nat) (u1 u2:T.expr) : Prop :=
      forall (ss:StageSet.t),
      StageSet.ub n ss = true ->
      (M.ssubst n (match n with
	  | S (S n) => if ltb h (b + m) 
       		then StageSet.add (S n) ss else ss
	  | _ => ss
          end) (M.cast_var (hole_var h)) u1 v) = u2.

  Definition eq_context_ssubst := congr_context_ssubst eq_ssubst.
  Definition eq_stack_ssubst := congr_stack_ssubst eq_ssubst.

  Definition eq_ssubst_2 (n:nat) (h:CRaw.var) 
      (m:nat) (v:T.expr) (b:nat) (u1 u2:T.expr) : Prop :=
      forall (ss:StageSet.t),
      StageSet.ub n ss = true ->
      (M.ssubst n (match n with
	  | S n => if ltb h (b + m) 
       		then StageSet.add n ss else ss
	  | _ => ss
          end) (M.cast_var (hole_var h)) u1 v) = u2.

  Definition eq_context_ssubst_2 := congr_context_ssubst eq_ssubst_2.
  Definition eq_stack_ssubst_2 := congr_stack_ssubst eq_ssubst_2.

  Lemma eq_ssubst_m_Sm:
    forall (e:T.expr) (b:nat) (h:S.var) (v:T.expr) (n m:nat),
    eq_ssubst n h m v b e e -> eq_ssubst n h (S m) v b e e.
  Proof.
    unfold eq_ssubst ; intros.
    case_beq_nat h (b + m)%nat.
    assert(ltb (b+m)%nat (b + m)%nat = false) as LtbFalse.
    apply leb_iff_conv ; omega.
    rewrite LtbFalse in H.
    assert(ltb (b+m)%nat (b + S m)%nat = true) as LtbTrue.
    apply leb_iff ; omega.
    rewrite LtbTrue.
    destruct n.
    apply H ; auto.
    destruct n.
    apply H ; auto.
    apply H ; auto.
    rewrite <- StageSetProperties.ub_le_1 ; auto.
    assert(ltb h (b + S m) = ltb h (b + m)) as Eq1.
    generalize E ; clear ; intros.
    remember (ltb h (b + m)) ; destruct b0 ; symmetry in Heqb0 ;
    [apply leb_iff ; apply leb_iff in Heqb0 | 
    apply leb_iff_conv ; apply leb_iff_conv in Heqb0] ; omega.
    rewrite Eq1 ; apply H ; auto.
  Qed.

  Lemma eq_ssubst_2_m_Sm:
    forall (e:T.expr) (b:nat) (h:S.var) (v:T.expr) (n m:nat),
    eq_ssubst_2 n h m v b e e -> eq_ssubst_2 n h (S m) v b e e.
  Proof.
    unfold eq_ssubst_2 ; intros.
    case_beq_nat h (b + m)%nat.
    assert(ltb (b+m)%nat (b + m)%nat = false) as LtbFalse.
    apply leb_iff_conv ; omega.
    rewrite LtbFalse in H.
    assert(ltb (b+m)%nat (b + S m)%nat = true) as LtbTrue.
    apply leb_iff ; omega.
    rewrite LtbTrue.
    destruct n.
    apply H ; auto.
    apply H ; auto.
    rewrite <- StageSetProperties.ub_le_1 ; auto.
    destruct n.
    apply H ; auto.
    assert(ltb h (b + S m) = ltb h (b + m)) as Eq1.
    generalize E ; clear ; intros.
    remember (ltb h (b + m)) ; destruct b0 ; symmetry in Heqb0 ;
    [apply leb_iff ; apply leb_iff in Heqb0 | 
    apply leb_iff_conv ; apply leb_iff_conv in Heqb0] ; omega.
    rewrite Eq1 ; apply H ; auto.
  Qed.

  Lemma eq_ssubst_m_ge:
    forall (e:T.expr) (b:nat) (h:S.var) (v:T.expr) (n m p:nat),
    eq_ssubst n h m v b e e -> 
    m <= p -> eq_ssubst n h p v b e e.
  Proof.
    intros.
    induction H0 ; auto.
    apply eq_ssubst_m_Sm ; auto.
  Qed.

  Lemma eq_ssubst_2_m_ge:
    forall (e:T.expr) (b:nat) (h:S.var) (v:T.expr) (n m p:nat),
    eq_ssubst_2 n h m v b e e -> 
    m <= p -> eq_ssubst_2 n h p v b e e.
  Proof.
    intros.
    induction H0 ; auto.
    apply eq_ssubst_2_m_Sm ; auto.
  Qed.

  Lemma eq_context_ssubst_m_ge:
    forall (c:Context.t) (b1 b2:nat) (h:S.var) (v:T.expr) (n m p:nat),
    eq_context_ssubst n h m v b1 b2 c c -> 
    m <= p -> eq_context_ssubst n h p v b1 b2 c c.
  Proof.
    intros.
    induction c ; auto.
    constructor.
    inversion H ; subst.
    constructor ; auto.
    apply eq_ssubst_m_ge with (m:=m) ; auto.
    apply IHc ; auto.
  Qed.

  Lemma eq_context_ssubst_2_m_ge:
    forall (c:Context.t) (b1 b2:nat) (h:S.var) (v:T.expr) (n m p:nat),
    eq_context_ssubst_2 n h m v b1 b2 c c -> 
    m <= p -> eq_context_ssubst_2 n h p v b1 b2 c c.
  Proof.
    intros.
    induction c ; auto.
    constructor.
    inversion H ; subst.
    constructor ; auto.
    apply eq_ssubst_2_m_ge with (m:=m) ; auto.
    apply IHc ; auto.
  Qed.

  Lemma eq_ssubst_fill_gt_1_strong:
    forall (e:S.expr) (bs:list nat) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) in
    match cs with
    | c1 :: nil => 
      match c1 with
      | nil => False
      | _ => forall (m:nat), 
        0 < m < length bs ->
        let b := hd 0 bs in
        eq_context_ssubst m h 0 v b 0 c1 c1 ->
        forall (ss:StageSet.t),
        StageSet.ub m ss = true ->
        (M.ssubst (S m) (match (S m) with
	  | S (S m) => if ltb h (length c1)
       		then StageSet.add (S m) 
                (match m with
                | 0 => ss
                | S m0 =>
                    if ltb h (b + 0) then StageSet.add (S m0) ss else ss
                end)
                else 
                (match m with
                | 0 => ss
                | S m0 =>
                    if ltb h (b + 0) then StageSet.add (S m0) ss else ss
                end)
	  | _ => (match m with
                | 0 => ss
                | S m0 =>
                    if ltb h (b + 0) then StageSet.add (S m0) ss else ss
                end)
          end) (M.cast_var (hole_var h)) e0 v) = e0 ->
        (M.ssubst m (match m with
	  | S (S m) => if ltb h (b + 0) 
       		then StageSet.add (S m) ss else ss
	  | _ => ss
          end) (M.cast_var (hole_var h)) (Context.fill c1 (ret (cast_ebox e0))) v) = 
          (Context.fill c1 (ret (cast_ebox e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (context_stack_not_nil e (0::bs)) ; intros CSNotNil.
    destruct (trans e (0::bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t ; auto.
    exfalso ; apply CSNotNil ; simpl ; auto.
    simpl ; intros.

    simpl in *|-*.
    inversion H0.
    subst c1 u2 c2 p.
    clear H0 CSNotNil.
    destruct bs ; [exfalso ; generalize H ; clear ; simpl ; intros ; omega|].
    simpl in *|-*.
    generalize dependent u1 ; generalize dependent ss.
    induction t ; simpl ; unfold eq_ssubst ; intros.

    destruct m ; [exfalso ; omega|].
    rewrite MP.ssubst_bind with (f2:=
    (fun v0 : T.expr =>
      cast_eapp (cast_eabs (cast_var (hole_var 0)) (ret (cast_ebox e0))) v0)).
    rewrite H6 ; auto.
    intros.
    rewrite MP.ssubst_eapp, MP.ssubst_eabs, MP.ssubst_ret, MP.ssubst_ebox.
    simpl in *|-*.

    assert(beq_var (hole_var h) (hole_var 0) = ltb h 1) as Eq1.
    clear ; simpl ; remember (ltb h 1) ; destruct b ; symmetry in Heqb.
    apply beq_nat_true_iff ; apply leb_iff in Heqb ; unfold hole_var ; omega.
    apply beq_nat_false_iff ; apply leb_iff_conv in Heqb ; unfold hole_var ; omega.
    destruct m ; destruct (ltb h (n + 0)) ; rewrite Eq1, H2 ; auto.

    inversion H8 ; clear H8.
    subst c1 u2 c2 a.
    destruct m ; [exfalso ; omega|].

    rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr =>
     cast_eapp
     (cast_eabs (cast_var (hole_var (S (length t))))
        (bind u0
           (fun v1 : T.expr =>
            cast_eapp
              (cast_eabs (cast_var (hole_var (length t)))
                 (Context.fill t (ret (cast_ebox e0)))) v1))) v0)).
    rewrite H6 ; auto.
    intros.
    rewrite MP.ssubst_eapp, MP.ssubst_eabs.
    simpl in *|-*.

      (* Case h = S length t *)
      case_beq_nat h (S (length t)).
      rewrite <- beq_nat_refl.
      assert(ltb (S (length t)) (S (length t)) = false) as False1.
      apply leb_iff_conv ; omega.
      rewrite False1 in IHt.
      assert(ltb (S (length t)) (S (S (length t))) = true) as True1.
      apply leb_iff ; omega.
      rewrite True1 in H2.
      destruct m ; [| destruct (ltb (S (length t)) (n + 0)) ] ;
      try(rewrite StageSetProperties.add_add) ; rewrite IHt ; auto ;
      try(rewrite StageSetProperties.add_mem_4 ; auto) ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto).
      rewrite StageSetProperties.add_add ; auto.

      (* Case h < S length t *)
      assert(beq_var (hole_var h) (hole_var (S (length t))) = false) as False1.
      apply beq_nat_false_iff ; unfold hole_var ; omega.
      rewrite False1, IHt ; auto.
      assert(ltb h (S (length t)) = ltb h (S (S (length t)))) as Eq1.
      remember (ltb h (S (S (length t)))) ; destruct b ; symmetry in Heqb.
      apply leb_iff ; apply leb_iff in Heqb ; omega.
      apply leb_iff_conv ; apply leb_iff_conv in Heqb ; omega.
      rewrite Eq1 ; auto.
  Qed.

  Lemma eq_ssubst_fill_gt_1:
    forall (e:S.expr) (bs:list nat) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) in
    match cs with
    | c1 :: nil => 
      match c1 with
      | nil => False
      | _ => forall (m:nat), 
        0 < m < length bs ->
        let b := hd 0 bs in
        eq_ssubst (S m) h (length c1) v 0 e0 e0 ->
        eq_context_ssubst m h 0 v b 0 c1 c1 ->
        eq_ssubst m h 0 v b
        (Context.fill c1 (ret (cast_ebox e0))) (Context.fill c1 (ret (cast_ebox e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (eq_ssubst_fill_gt_1_strong e bs) ; intros Strong1.
    specialize (context_stack_not_nil e (0::bs)) ; intros CSNotNil.
    destruct (trans e (0::bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t ; auto.
    unfold eq_ssubst ; intros.
    apply Strong1 ; auto.
    simpl plus in *|-* ; simpl length in *|-*.
    destruct m.
    apply H0 ; auto.
    rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto.
    destruct m.
    apply H0 ; auto.
    rewrite StageSetProperties.ub_le_2 with (m:=1) ; auto.
    apply H0 ; auto.
    destruct (ltb h (hd 0 bs + 0)) ; [
    rewrite <- StageSetProperties.ub_le_1 ; auto |] ;
    rewrite StageSetProperties.ub_le_2 with (m:=S (S m)) ; auto.
  Qed.

  Lemma eq_ssubst_fill_ge_2_strong:
    forall (e:S.expr) (bs:list nat) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) in
    match cs with
    | c1 :: c1' :: cs => 
      match c1 with
      | nil => False
      | _ => forall (m:nat), 
        S (length cs) <= m < length bs ->
        let b := hd 0 bs in
        eq_context_ssubst m h (length c1') v b 0 c1 c1 ->
        forall (ss:StageSet.t),
        StageSet.ub m ss = true ->
        (M.ssubst (S m) (match (S m) with
	  | S (S m) => if ltb h (0 + (length c1)) 
       		then StageSet.add (S m) (match m with
                  | 0 => ss
                  | S m0 =>
                      if ltb h (b + length c1')
                      then StageSet.add (S m0) ss
                      else ss
                  end) else (match m with
                  | 0 => ss
                  | S m0 =>
                      if ltb h (b + length c1')
                      then StageSet.add (S m0) ss
                      else ss
                  end)
	  | _ => ss
          end) (M.cast_var (hole_var h)) e0 v) = e0 ->


        (M.ssubst m (match m with
	  | S (S m) => if ltb h (b + (length c1')) 
       		then StageSet.add (S m) ss else ss
	  | _ => ss
          end) (M.cast_var (hole_var h)) (Context.fill c1 (ret (cast_ebox e0))) v) = 
          (Context.fill c1 (ret (cast_ebox e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (context_stack_not_nil e (0::bs)) ; intros CSNotNil.
    destruct (trans e (0::bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t ; auto.
    exfalso ; apply CSNotNil ; simpl ; auto.
    simpl ; intros.

    simpl in *|-*.
    
    inversion H0.
    subst c1 u2 c2 p.
    clear H0 CSNotNil.
    destruct bs ; [exfalso ; generalize H ; clear ; simpl ; intros ; omega|].
    simpl in *|-*.
    generalize dependent u1 ; generalize dependent ss.
    induction t ; simpl ; unfold eq_ssubst ; intros.

    destruct m ; [exfalso ; omega|].
    rewrite MP.ssubst_bind with (f2:=
    (fun v0 : T.expr =>
      cast_eapp (cast_eabs (cast_var (hole_var 0)) (ret (cast_ebox e0))) v0)).
    rewrite H6 ; auto.
    intros.
    rewrite MP.ssubst_eapp, MP.ssubst_eabs, MP.ssubst_ret, MP.ssubst_ebox.
    simpl in *|-*.

    assert(beq_var (hole_var h) (hole_var 0) = ltb h 1) as Eq1.
    clear ; simpl ; remember (ltb h 1) ; destruct b ; symmetry in Heqb.
    apply beq_nat_true_iff ; apply leb_iff in Heqb ; unfold hole_var ; omega.
    apply beq_nat_false_iff ; apply leb_iff_conv in Heqb ; unfold hole_var ; omega.
    destruct m ; destruct (ltb h (n + (length t0))) ; rewrite Eq1, H2 ; auto.

    inversion H8 ; clear H8.
    subst c1 u2 c2 a.
    destruct m ; [exfalso ; omega|].

    rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr =>
     cast_eapp
     (cast_eabs (cast_var (hole_var (S (length t))))
        (bind u0
           (fun v1 : T.expr =>
            cast_eapp
              (cast_eabs (cast_var (hole_var (length t)))
                 (Context.fill t (ret (cast_ebox e0)))) v1))) v0)).
    rewrite H6 ; auto.
    intros.
    rewrite MP.ssubst_eapp, MP.ssubst_eabs.
    simpl in *|-*.

      (* Case h = S length t *)
      case_beq_nat h (S (length t)).
      rewrite <- beq_nat_refl.
      assert(ltb (S (length t)) (S (length t)) = false) as False1.
      apply leb_iff_conv ; omega.
      rewrite False1 in IHt.
      assert(ltb (S (length t)) (S (S (length t))) = true) as True1.
      apply leb_iff ; omega.
      rewrite True1 in H2.
      destruct m ; [| destruct (ltb (S (length t)) (n + (length t0))) ] ;
      try(rewrite StageSetProperties.add_add) ; rewrite IHt ; auto ;
      try(rewrite StageSetProperties.add_mem_4 ; auto) ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto).
      rewrite StageSetProperties.add_add ; auto.

      (* Case h < S length t *)
      assert(beq_var (hole_var h) (hole_var (S (length t))) = false) as False1.
      apply beq_nat_false_iff ; unfold hole_var ; omega.
      rewrite False1, IHt ; auto.
      assert(ltb h (S (length t)) = ltb h (S (S (length t)))) as Eq1.
      remember (ltb h (S (S (length t)))) ; destruct b ; symmetry in Heqb.
      apply leb_iff ; apply leb_iff in Heqb ; omega.
      apply leb_iff_conv ; apply leb_iff_conv in Heqb ; omega.
      rewrite Eq1 ; auto.
  Qed.

  Lemma eq_ssubst_fill_gt_2:
    forall (e:S.expr) (bs:list nat) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) in
    match cs with
    | c1 :: c1' :: cs => 
      match c1 with
      | nil => False
      | _ => forall (m:nat), 
        S (length cs) < m < length bs ->
        let b := hd 0 bs in
        eq_ssubst (S m) h (length c1) v 0 e0 e0 ->
        eq_context_ssubst m h (length c1') v b 0 c1 c1 ->
        eq_ssubst m h (length c1') v b
        (Context.fill c1 (ret (cast_ebox e0))) (Context.fill c1 (ret (cast_ebox e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (eq_ssubst_fill_ge_2_strong e bs) ; intros Strong1.
    specialize (context_stack_not_nil e (0::bs)) ; intros CSNotNil.
    destruct (trans e (0::bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t ; auto.
    unfold eq_ssubst ; intros.
    apply Strong1 ; auto.
    simpl plus in *|-* ; simpl length in *|-*.
    omega.
    destruct m.
    apply H0 ; auto.
    rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto.
    destruct m.
    apply H0 ; auto.
    rewrite StageSetProperties.ub_le_2 with (m:=1) ; auto.
    apply H0 ; auto.
    destruct (ltb h (hd 0 bs + (length t0))) ; [
    rewrite <- StageSetProperties.ub_le_1 ; auto |] ;
    rewrite StageSetProperties.ub_le_2 with (m:=S (S m)) ; auto.
  Qed.

  Lemma eq_ssubst_2_fill_ge_1_strong:
    forall (e:S.expr) (bs:list nat) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) in
    match cs with
    | c1 :: nil => 
      match c1 with
      | nil => False
      | _ => forall (m:nat), 
        0 <= m < length bs ->
        let b := hd 0 bs in
        eq_context_ssubst_2 m h 0 v b 0 c1 c1 ->
        forall (ss:StageSet.t),
        StageSet.ub m ss = true ->
        (M.ssubst (S m) (match (S m) with
	  | S m => if ltb h (length c1)
       		then StageSet.add m 
                (match m with
                | 0 => ss
                | S m0 =>
                    if ltb h (b + 0) then StageSet.add m0 ss else ss
                end)
                else 
                (match m with
                | 0 => ss
                | S m0 =>
                    if ltb h (b + 0) then StageSet.add m0 ss else ss
                end)
	  | _ => (match m with
                | 0 => ss
                | S m0 =>
                    if ltb h (b + 0) then StageSet.add m0 ss else ss
                end)
          end)  (M.cast_var (hole_var h)) e0 v) = e0 ->
        (M.ssubst m (match m with
	  | S m => if ltb h (b + 0) 
       		then StageSet.add m ss else ss
	  | _ => ss
          end) (M.cast_var (hole_var h)) (Context.fill c1 (ret (cast_ebox e0))) v) = 
          (Context.fill c1 (ret (cast_ebox e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (context_stack_not_nil e (0::bs)) ; intros CSNotNil.
    destruct (trans e (0::bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t ; auto.
    exfalso ; apply CSNotNil ; simpl ; auto.
    simpl ; intros.

    simpl in *|-*.
    inversion H0.
    subst c1 u2 c2 p.
    clear H0 CSNotNil.
    destruct bs ; [exfalso ; generalize H ; clear ; simpl ; intros ; omega|].
    simpl in *|-*.
    generalize dependent u1 ; generalize dependent ss.
    induction t ; simpl ; unfold eq_ssubst_2 ; intros.

    rewrite MP.ssubst_bind with (f2:=
    (fun v0 : T.expr =>
      cast_eapp (cast_eabs (cast_var (hole_var 0)) (ret (cast_ebox e0))) v0)).
    rewrite H6 ; auto.
    intros.
    rewrite MP.ssubst_eapp, MP.ssubst_eabs, MP.ssubst_ret, MP.ssubst_ebox.
    simpl in *|-*.

    assert(beq_var (hole_var h) (hole_var 0) = ltb h 1) as Eq1.
    clear ; simpl ; remember (ltb h 1) ; destruct b ; symmetry in Heqb.
    apply beq_nat_true_iff ; apply leb_iff in Heqb ; unfold hole_var ; omega.
    apply beq_nat_false_iff ; apply leb_iff_conv in Heqb ; unfold hole_var ; omega.
    destruct m ; destruct (ltb h (n + 0)) ; rewrite Eq1, H2 ; auto.

    inversion H8 ; clear H8.
    subst c1 u2 c2 a.

    rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr =>
     cast_eapp
     (cast_eabs (cast_var (hole_var (S (length t))))
        (bind u0
           (fun v1 : T.expr =>
            cast_eapp
              (cast_eabs (cast_var (hole_var (length t)))
                 (Context.fill t (ret (cast_ebox e0)))) v1))) v0)).
    rewrite H6 ; auto.
    intros.
    rewrite MP.ssubst_eapp, MP.ssubst_eabs.
    simpl in *|-*.

      (* Case h = S length t *)
      case_beq_nat h (S (length t)).
      rewrite <- beq_nat_refl.
      assert(ltb (S (length t)) (S (length t)) = false) as False1.
      apply leb_iff_conv ; omega.
      rewrite False1 in IHt.
      assert(ltb (S (length t)) (S (S (length t))) = true) as True1.
      apply leb_iff ; omega.
      rewrite True1 in H2.
      destruct m ; [| destruct (ltb (S (length t)) (n + 0)) ] ;
      try(rewrite StageSetProperties.add_add) ; rewrite IHt ; auto ;
      try(rewrite StageSetProperties.add_mem_4 ; auto) ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto).
      rewrite StageSetProperties.add_add ; auto.

      (* Case h < S length t *)
      assert(beq_var (hole_var h) (hole_var (S (length t))) = false) as False1.
      apply beq_nat_false_iff ; unfold hole_var ; omega.
      rewrite False1, IHt ; auto.
      assert(ltb h (S (length t)) = ltb h (S (S (length t)))) as Eq1.
      remember (ltb h (S (S (length t)))) ; destruct b ; symmetry in Heqb.
      apply leb_iff ; apply leb_iff in Heqb ; omega.
      apply leb_iff_conv ; apply leb_iff_conv in Heqb ; omega.
      rewrite Eq1 ; auto.
  Qed.

  Lemma eq_ssubst_2_fill_ge_1:
    forall (e:S.expr) (bs:list nat) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) in
    match cs with
    | c1 :: nil => 
      match c1 with
      | nil => False
      | _ => forall (m:nat), 
        0 <= m < length bs ->
        let b := hd 0 bs in
        eq_ssubst_2 (S m) h (length c1) v 0 e0 e0 ->
        eq_context_ssubst_2 m h 0 v b 0 c1 c1 ->
        eq_ssubst_2 m h 0 v b
        (Context.fill c1 (ret (cast_ebox e0))) (Context.fill c1 (ret (cast_ebox e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (eq_ssubst_2_fill_ge_1_strong e bs) ; intros Strong1.
    specialize (context_stack_not_nil e (0::bs)) ; intros CSNotNil.
    destruct (trans e (0::bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t ; auto.
    unfold eq_ssubst_2 ; intros.
    apply Strong1 ; auto.
    simpl plus in *|-* ; simpl length in *|-*.
    destruct m.
    apply H0 ; auto.
    rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto.
    apply H0 ; auto.
    destruct (ltb h (hd 0 bs + 0)) ; [
    rewrite <- StageSetProperties.ub_le_1 ; auto |] ;
    rewrite StageSetProperties.ub_le_2 with (m:=S m) ; auto.
  Qed.


  Lemma eq_ssubst_2_fill_ge_2_strong:
    forall (e:S.expr) (bs:list nat) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) in
    match cs with
    | c1 :: c1' :: cs => 
      match c1 with
      | nil => False
      | _ => forall (m:nat), 
        S (length cs) <= m < length bs ->
        let b := hd 0 bs in
        eq_context_ssubst_2 m h (length c1') v b 0 c1 c1 ->
        forall (ss:StageSet.t),
        StageSet.ub m ss = true ->
        (M.ssubst (S m) (match (S m) with
	  | S (S m) => if ltb h (0 + (length c1)) 
       		then StageSet.add (S m) (if ltb h (b + length c1')
                      then StageSet.add m ss
                      else ss) 
                else (if ltb h (b + length c1') then StageSet.add m ss
                      else ss)
	  | _ => ss
          end) (M.cast_var (hole_var h)) e0 v) = e0 ->

        (M.ssubst m (match m with
	  | S m => if ltb h (b + (length c1')) 
       		then StageSet.add m ss else ss
	  | _ => ss
          end) (M.cast_var (hole_var h)) (Context.fill c1 (ret (cast_ebox e0))) v) = 
          (Context.fill c1 (ret (cast_ebox e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (context_stack_not_nil e (0::bs)) ; intros CSNotNil.
    destruct (trans e (0::bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t ; auto.
    exfalso ; apply CSNotNil ; simpl ; auto.
    simpl ; intros.

    simpl in *|-*.
    
    inversion H0.
    subst c1 u2 c2 p.
    clear H0 CSNotNil.
    destruct bs ; [exfalso ; generalize H ; clear ; simpl ; intros ; omega|].
    simpl in *|-*.
    generalize dependent u1 ; generalize dependent ss.
    induction t ; simpl ; unfold eq_ssubst ; intros.

    destruct m ; [exfalso ; omega|].
    rewrite MP.ssubst_bind with (f2:=
    (fun v0 : T.expr =>
      cast_eapp (cast_eabs (cast_var (hole_var 0)) (ret (cast_ebox e0))) v0)).
    rewrite H6 ; auto.
    intros.
    rewrite MP.ssubst_eapp, MP.ssubst_eabs, MP.ssubst_ret, MP.ssubst_ebox.
    simpl in *|-*.

    assert(beq_var (hole_var h) (hole_var 0) = ltb h 1) as Eq1.
    clear ; simpl ; remember (ltb h 1) ; destruct b ; symmetry in Heqb.
    apply beq_nat_true_iff ; apply leb_iff in Heqb ; unfold hole_var ; omega.
    apply beq_nat_false_iff ; apply leb_iff_conv in Heqb ; unfold hole_var ; omega.
    destruct m ; destruct (ltb h (n + (length t0))) ; rewrite Eq1, H2 ; auto.

    inversion H8 ; clear H8.
    subst c1 u2 c2 a.
    destruct m ; [exfalso ; omega|].

    rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr =>
     cast_eapp
     (cast_eabs (cast_var (hole_var (S (length t))))
        (bind u0
           (fun v1 : T.expr =>
            cast_eapp
              (cast_eabs (cast_var (hole_var (length t)))
                 (Context.fill t (ret (cast_ebox e0)))) v1))) v0)).
    rewrite H6 ; auto.
    intros.
    rewrite MP.ssubst_eapp, MP.ssubst_eabs.
    simpl in *|-*.

      (* Case h = S length t *)
      case_beq_nat h (S (length t)).
      rewrite <- beq_nat_refl.
      assert(ltb (S (length t)) (S (length t)) = false) as False1.
      apply leb_iff_conv ; omega.
      rewrite False1 in IHt.
      assert(ltb (S (length t)) (S (S (length t))) = true) as True1.
      apply leb_iff ; omega.
      rewrite True1 in H2.
      destruct (ltb (S (length t)) (n + (length t0))) ;
      try(rewrite StageSetProperties.add_add) ; rewrite IHt ; auto ;
      try(rewrite StageSetProperties.add_mem_4 ; auto) ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto).
      rewrite StageSetProperties.add_add ; auto.

      (* Case h < S length t *)
      assert(beq_var (hole_var h) (hole_var (S (length t))) = false) as False1.
      apply beq_nat_false_iff ; unfold hole_var ; omega.
      rewrite False1, IHt ; auto.
      assert(ltb h (S (length t)) = ltb h (S (S (length t)))) as Eq1.
      remember (ltb h (S (S (length t)))) ; destruct b ; symmetry in Heqb.
      apply leb_iff ; apply leb_iff in Heqb ; omega.
      apply leb_iff_conv ; apply leb_iff_conv in Heqb ; omega.
      rewrite Eq1 ; auto.
  Qed.

  Lemma eq_ssubst_2_fill_ge_2:
    forall (e:S.expr) (bs:list nat) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) in
    match cs with
    | c1 :: c1' :: cs => 
      match c1 with
      | nil => False
      | _ => forall (m:nat), 
        S (length cs) <= m < length bs ->
        let b := hd 0 bs in
        eq_ssubst_2 (S m) h (length c1) v 0 e0 e0 ->
        eq_context_ssubst_2 m h (length c1') v b 0 c1 c1 ->
        eq_ssubst_2 m h (length c1') v b
        (Context.fill c1 (ret (cast_ebox e0))) (Context.fill c1 (ret (cast_ebox e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (eq_ssubst_2_fill_ge_2_strong e bs) ; intros Strong1.
    specialize (context_stack_not_nil e (0::bs)) ; intros CSNotNil.
    destruct (trans e (0::bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t ; auto.
    unfold eq_ssubst_2 ; intros.
    apply Strong1 ; auto.
    simpl plus in *|-* ; simpl length in *|-*.
    clear Strong1 CSNotNil.
    destruct m ; [exfalso ; omega|].
    apply H0 ; auto.

    destruct (ltb h (hd 0 bs + (length t0))) ; [
    rewrite <- StageSetProperties.ub_le_1 ; auto |] ;
    rewrite StageSetProperties.ub_le_2 with (m:=S m) ; auto.
  Qed.

  Lemma eq_ssubst_sum:
    forall (e v:T.expr) (n m1 m2 b1 b2:nat) (h:S.var),
    eq_ssubst n h m1 v b1 e e ->
    (b1 + m1 = b2 + m2)%nat ->
    eq_ssubst n h m2 v b2 e e.
  Proof.
    unfold eq_ssubst ; intros.
    rewrite <- H0.
    apply H ; auto.
  Qed.

  Lemma eq_ssubst_2_sum:
    forall (e v:T.expr) (n m1 m2 b1 b2:nat) (h:S.var),
    eq_ssubst_2 n h m1 v b1 e e ->
    (b1 + m1 = b2 + m2)%nat ->
    eq_ssubst_2 n h m2 v b2 e e.
  Proof.
    unfold eq_ssubst_2 ; intros.
    rewrite <- H0.
    apply H ; auto.
  Qed.

  Lemma eq_context_ssubst_sum:
    forall (c:Context.t) (v:T.expr) (n m1 m2 b1 b2 b3:nat) (h:S.var),
    eq_context_ssubst n h m1 v b1 b3 c c ->
    (b1 + m1 = b2 + m2)%nat ->
    eq_context_ssubst n h m2 v b2 b3 c c.
  Proof.
    induction c ; simpl ; intros.
    constructor.
    inversion H ; subst.
    constructor ; auto.
    apply eq_ssubst_sum with (m1:=m1) (b1:=b1) ; auto.
    apply IHc with (m1:=m1) (b1:=b1) ; auto.
  Qed.

  Lemma eq_context_ssubst_2_sum:
    forall (c:Context.t) (v:T.expr) (n m1 m2 b1 b2 b3:nat) (h:S.var),
    eq_context_ssubst_2 n h m1 v b1 b3 c c ->
    (b1 + m1 = b2 + m2)%nat ->
    eq_context_ssubst_2 n h m2 v b2 b3 c c.
  Proof.
    induction c ; simpl ; intros.
    constructor.
    inversion H ; subst.
    constructor ; auto.
    apply eq_ssubst_2_sum with (m1:=m1) (b1:=b1) ; auto.
    apply IHc with (m1:=m1) (b1:=b1) ; auto.
  Qed.

  Lemma eq_ssubst_merge:
    forall (e1 e2:S.expr) (bs:list nat) (h:S.var) (v:T.expr),
    let (e1', cs1) := trans e1 (map_iter_booker e2 bs 0) in
    let (e2', cs2) := trans e2 bs in
    forall (m:nat),
    max (depth e1) (depth e2) <= m < length bs ->
    eq_stack_ssubst (pred m) h v (tl (map_iter_booker e2 bs 0))
       (hd 0 (map_iter_booker e2 bs 0)) cs1 cs1 ->
    eq_stack_ssubst (pred m) h v (tl bs) (hd 0 bs) cs2 cs2 ->
    eq_stack_ssubst (pred m) h v (tl bs) (hd 0 bs) (Context.merge cs1 cs2)
      (Context.merge cs1 cs2).
  Proof.
    intros.
    specialize (map_iter_booker_stack e2 bs) ; intros MapIterBooker2.
    specialize (depth_length e1 (map_iter_booker e2 bs 0)) ; intros DpthLength1.
    specialize (depth_length e2 bs) ; intros DpthLength2.
    destruct (trans e1) ; destruct (trans e2) ; intros.
    rewrite DpthLength1, DpthLength2 in H ; clear DpthLength1 DpthLength2.
    rewrite MapIterBooker2 in H0 ; clear MapIterBooker2.
    
    generalize dependent m ; generalize dependent t ;
    generalize dependent bs.
    induction t0 ; simpl ; intros ; auto.
    rewrite ContextStaticProperties.merge_nil_r ; simpl ; auto.
    destruct bs ; [exfalso ; simpl in *|-* ; omega|].

    assert(forall (bs:list nat) (m:nat), bs = 
      (tl (map_iter_stack nil (n :: bs) m))) as Eq1.
    induction bs0 ; simpl in *|-* ; intros ; auto.
    rewrite <- IHbs0 ; auto.
    rewrite plus_0_r ; simpl ; auto.

    rewrite <- Eq1 in H0.
    simpl in *|-* ; rewrite plus_0_r in H0 ; auto.

    destruct bs ; [exfalso ; simpl in *|-* ; omega|].
    destruct t ; [simpl in *|-* |] ; auto.
    destruct m ; [simpl in *|-* ; exfalso ; omega|].
    destruct bs ; [exfalso ; simpl in *|-* ; omega|].

    specialize (IHt0 (n0::bs) t1).
    simpl in IHt0.
    assert(eq_stack_ssubst (pred m) h v bs n0 (Context.merge t1 t0)
         (Context.merge t1 t0)) as IH.
    apply IHt0 ; auto.
    simpl in H ; omega.

    
    assert(forall (bs:list nat) (n0 m:nat), 
      map_iter_stack t0 (n0 :: bs) m = 
      tl (map_iter_stack (a :: t0) (n :: n0 :: bs) m)) as Eq2.
    induction bs0 ; simpl in *|-* ; intros ; auto.
    unfold map_iter_stack in *|-* ; simpl.
    specialize (IHbs0 a0 (S m0)).
    simpl in IHbs0.
    rewrite IHbs0 ; auto.
    rewrite <- Eq2 in H0.
    inversion H0 ; subst ; auto.
    constructor.

    simpl in *|-*.
    inversion H1 ; subst ; auto.
    constructor.
    clear IHt0.

    simpl in *|-*.

    inversion H0 ; subst ; [simpl in *|-*|].
    inversion H1 ; subst ; simpl in *|-*.
    constructor ; auto.
    apply congr_ssubst_context_app ; auto.
    rewrite plus_0_r in H5 ; auto.

    constructor ; auto.
    apply congr_ssubst_context_app ; auto.
    apply eq_context_ssubst_sum with (m1:=0) (b1:=(n0 + length c1')%nat) ; auto.

    inversion H1 ; subst.
    simpl ; constructor ; auto.
    apply congr_ssubst_context_app ; simpl in *|-* ; auto.
    simpl in *|-* ; rewrite plus_0_r in H6 ; auto.
    apply eq_context_ssubst_m_ge with (m:=0) ; auto ; omega.

    constructor ; auto.
    apply congr_ssubst_context_app ; auto.

    simpl in *|-* ; auto.
    apply eq_context_ssubst_sum with (m1:=length c1') (b1:=(n0 + length c1'0)%nat) ; auto.
    rewrite app_length ; omega.

    apply eq_context_ssubst_m_ge with (m:=length c1'0) ; auto.
    rewrite app_length ; omega.
  Qed.

  Lemma eq_ssubst_2_merge:
    forall (e1 e2:S.expr) (bs:list nat) (h:S.var) (v:T.expr),
    let (e1', cs1) := trans e1 (map_iter_booker e2 bs 0) in
    let (e2', cs2) := trans e2 bs in
    forall (m:nat),
    max (depth e1) (depth e2) <= m < length bs ->
    eq_stack_ssubst_2 (pred m) h v (tl (map_iter_booker e2 bs 0))
       (hd 0 (map_iter_booker e2 bs 0)) cs1 cs1 ->
    eq_stack_ssubst_2 (pred m) h v (tl bs) (hd 0 bs) cs2 cs2 ->
    eq_stack_ssubst_2 (pred m) h v (tl bs) (hd 0 bs) (Context.merge cs1 cs2)
      (Context.merge cs1 cs2).
  Proof.
    intros.
    specialize (map_iter_booker_stack e2 bs) ; intros MapIterBooker2.
    specialize (depth_length e1 (map_iter_booker e2 bs 0)) ; intros DpthLength1.
    specialize (depth_length e2 bs) ; intros DpthLength2.
    destruct (trans e1) ; destruct (trans e2) ; intros.
    rewrite DpthLength1, DpthLength2 in H ; clear DpthLength1 DpthLength2.
    rewrite MapIterBooker2 in H0 ; clear MapIterBooker2.
    
    generalize dependent m ; generalize dependent t ;
    generalize dependent bs.
    induction t0 ; simpl ; intros ; auto.
    rewrite ContextStaticProperties.merge_nil_r ; simpl ; auto.
    destruct bs ; [exfalso ; simpl in *|-* ; omega|].

    assert(forall (bs:list nat) (m:nat), bs = 
      (tl (map_iter_stack nil (n :: bs) m))) as Eq1.
    induction bs0 ; simpl in *|-* ; intros ; auto.
    rewrite <- IHbs0 ; auto.
    rewrite plus_0_r ; simpl ; auto.

    rewrite <- Eq1 in H0.
    simpl in *|-* ; rewrite plus_0_r in H0 ; auto.

    destruct bs ; [exfalso ; simpl in *|-* ; omega|].
    destruct t ; [simpl in *|-* |] ; auto.
    destruct m ; [simpl in *|-* ; exfalso ; omega|].
    destruct bs ; [exfalso ; simpl in *|-* ; omega|].

    specialize (IHt0 (n0::bs) t1).
    simpl in IHt0.
    assert(eq_stack_ssubst_2 (pred m) h v bs n0 (Context.merge t1 t0)
         (Context.merge t1 t0)) as IH.
    apply IHt0 ; auto.
    simpl in H ; omega.

    
    assert(forall (bs:list nat) (n0 m:nat), 
      map_iter_stack t0 (n0 :: bs) m = 
      tl (map_iter_stack (a :: t0) (n :: n0 :: bs) m)) as Eq2.
    induction bs0 ; simpl in *|-* ; intros ; auto.
    unfold map_iter_stack in *|-* ; simpl.
    specialize (IHbs0 a0 (S m0)).
    simpl in IHbs0.
    rewrite IHbs0 ; auto.
    rewrite <- Eq2 in H0.
    inversion H0 ; subst ; auto.
    constructor.

    simpl in *|-*.
    inversion H1 ; subst ; auto.
    constructor.
    clear IHt0.

    simpl in *|-*.

    inversion H0 ; subst ; [simpl in *|-*|].
    inversion H1 ; subst ; simpl in *|-*.
    constructor ; auto.
    apply congr_ssubst_context_app ; auto.
    rewrite plus_0_r in H5 ; auto.

    constructor ; auto.
    apply congr_ssubst_context_app ; auto.
    apply eq_context_ssubst_2_sum with (m1:=0) (b1:=(n0 + length c1')%nat) ; auto.

    inversion H1 ; subst.
    simpl ; constructor ; auto.
    apply congr_ssubst_context_app ; simpl in *|-* ; auto.
    simpl in *|-* ; rewrite plus_0_r in H6 ; auto.
    apply eq_context_ssubst_2_m_ge with (m:=0) ; auto ; omega.

    constructor ; auto.
    apply congr_ssubst_context_app ; auto.

    simpl in *|-* ; auto.
    apply eq_context_ssubst_2_sum with (m1:=length c1') (b1:=(n0 + length c1'0)%nat) ; auto.
    rewrite app_length ; omega.

    apply eq_context_ssubst_2_m_ge with (m:=length c1'0) ; auto.
    rewrite app_length ; omega.
  Qed.

  Lemma eq_ssubst_gt:
    forall (e:S.expr) (bs:list nat) (h:S.var) (v:T.expr),
    let n := depth e in
    let (e0, cs) := trans e bs in
    forall (m:nat), 
    n < m < length bs ->
    eq_ssubst m h (booker e 0) v (nth 0 bs 0) e0 e0 /\
    eq_stack_ssubst (pred m) h v 
                       (List.tl bs) (List.hd 0 bs) cs cs /\
    (svalue 0 e -> eq_ssubst m h (booker e 0) v (nth 0 bs 0) (phi e bs) (phi e bs)).
  Proof.
    assert(forall (h v:nat), beq_nat (hole_var h) (source_var v) = false) as BeqFalse.
      intros ; apply beq_nat_false_iff ; unfold hole_var, source_var ; omega.

    induction e ; simpl ; intros.

    (* EConst *)
    unfold eq_ssubst ; repeat(split) ; intros ;
    [rewrite MP.ssubst_ret | constructor |] ; 
    rewrite MP.ssubst_econst ; auto.

    
    (* EVar *)
    unfold eq_ssubst ; repeat(split) ; intros ;
    [rewrite MP.ssubst_ret | constructor |] ;
    rewrite MP.ssubst_evar, BeqFalse ; auto.

    (* EAbs *)
    specialize (IHe bs h v0) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ; [
    rewrite MP.ssubst_ret, MP.ssubst_eabs, BeqFalse, H1 |
    destruct H1 | rewrite MP.ssubst_eabs, BeqFalse, H2 ] ; auto.

    (* EFix *)
    specialize (IHe bs h v1) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ; [
    rewrite MP.ssubst_ret, MP.ssubst_efix, BeqFalse, BeqFalse ; simpl ; rewrite H1 |
    destruct H1 | rewrite MP.ssubst_efix, BeqFalse, BeqFalse ; simpl ; rewrite H2 ] ; auto.
    
    (* EApp *)
    specialize (eq_ssubst_merge e1 e2 bs h v) ; intros EqMerge.
    specialize (IHe1 (map_iter_booker e2 bs 0) h v) ;
    specialize (IHe2 bs h v) ;
    destruct (trans e1) ; destruct (trans e2) ; intros.
    unfold eq_ssubst ; repeat(split) ; intros.
    assert(nth 0 (map_iter_booker e2 bs 0) 0 + booker e1 0 =
     nth 0 bs 0 + (booker e1 0 + booker e2 0))%nat as EqNth.
     unfold map_iter_booker.
     specialize (List2Properties.map_iter_nth_indep 
      (fun b n : nat => (b + booker e2 n)%nat) bs 0 0 0) ; intros Prop1.
      rewrite Prop1 ; auto ; simpl ; omega.
     remember (CRaw.svalueb 0 e1) ; destruct b ; symmetry in Heqb.
    
      (* Case svalue 0 e1 *)
      destruct H ; apply max_lub_lt_iff in H ; auto ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto.
      rewrite MP.ssubst_bind with (f2:=(fun v2 : T.expr => cast_eapp (phi e1 (map_iter_booker e2 bs 0)) v2)).
      destruct m ; [rewrite H5 ; auto|].
      destruct m ; [rewrite H5 ; auto|].
      unfold eq_ssubst in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0)) ; 
      destruct b ; symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))%nat = true) as LtbTrue.
      apply leb_iff ; apply leb_iff in Heqb0 ; omega.
      rewrite LtbTrue, H5 ; auto.
      rewrite H5 ; auto.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))) ; auto.
      rewrite <- StageSetProperties.ub_le_1 ; auto.
      intros ; apply CalculusProperties.svalueb_iff in Heqb.
      rewrite MP.ssubst_eapp ; destruct H4.
      destruct m ; [rewrite H7 ; auto|].
      destruct m ; [rewrite H7 ; auto|].
      unfold eq_ssubst in H7.
      rewrite EqNth in H7 ; rewrite H7 ; auto.

      (* Case not svalue 0 e1 *)
      destruct H ; apply max_lub_lt_iff in H ; auto ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto.

      rewrite MP.ssubst_bind with (f2:=(fun v1 : T.expr => bind e0 (fun v2 : T.expr => cast_eapp v1 v2))).
      destruct m ; [rewrite H3 ; auto|].
      destruct m ; [rewrite H3 ; auto|].
      unfold eq_ssubst in H3.
      rewrite EqNth in H3 ; rewrite H3 ; auto.
      intros.
      rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr => cast_eapp (ssubst m
        match m with
        | 0 => ss
        | 1 => ss
        | S (S n) =>
            if ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))
            then StageSet.add (S n) ss
            else ss
        end (cast_var (hole_var h)) v2 v) v0)).
      destruct m ; [rewrite H5 ; auto |].
      destruct m ; [rewrite H5 ; auto |].
      unfold eq_ssubst in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0)) ; destruct b ;
      symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) = true) as LtbTrue.
      apply leb_iff ; apply leb_iff in Heqb0 ; omega.
      rewrite LtbTrue, H5 ; auto.
      rewrite H5 ; auto.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))) ; auto.
      rewrite <- StageSetProperties.ub_le_1 ; auto.
      intros ; rewrite MP.ssubst_eapp ; auto.

      destruct H ; apply max_lub_lt_iff in H ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto.
      destruct H5 ; destruct H3 ; clear H2 H4 H6 H7 IHe1 IHe2.
      apply EqMerge ; auto.
      split ; auto.
      apply max_lub_iff ; omega.
      inversion H0.

    (* ELoc *)
    unfold eq_ssubst ; repeat(split) ; intros ;
    [rewrite MP.ssubst_ret | constructor |] ; 
    rewrite MP.ssubst_eloc ; auto.

    (* ERef *)
    specialize (IHe bs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_eref v0)) ; 
    intros.
    rewrite H1 ; auto.
    rewrite MP.ssubst_eref ; reflexivity.
    destruct H1 ; auto.
    inversion H0.

    (* EDeref *)
    specialize (IHe bs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_ederef v0)) ; 
    intros.
    rewrite H1 ; auto.
    rewrite MP.ssubst_ederef ; reflexivity.
    destruct H1 ; auto.
    inversion H0.

    (* EAssign *)
    specialize (eq_ssubst_merge e1 e2 bs h v) ; intros EqMerge.
    specialize (IHe1 (map_iter_booker e2 bs 0) h v) ;
    specialize (IHe2 bs h v) ;
    destruct (trans e1) ; destruct (trans e2) ; intros.
    unfold eq_ssubst ; repeat(split) ; intros.
    assert(nth 0 (map_iter_booker e2 bs 0) 0 + booker e1 0 =
     nth 0 bs 0 + (booker e1 0 + booker e2 0))%nat as EqNth.
     unfold map_iter_booker.
     specialize (List2Properties.map_iter_nth_indep 
      (fun b n : nat => (b + booker e2 n)%nat) bs 0 0 0) ; intros Prop1.
      rewrite Prop1 ; auto ; simpl ; omega.
     remember (CRaw.svalueb 0 e1) ; destruct b ; symmetry in Heqb.
    
      (* Case svalue 0 e1 *)
      destruct H ; apply max_lub_lt_iff in H ; auto ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto.
      rewrite MP.ssubst_bind with (f2:=(fun v2 : T.expr => cast_eassign (phi e1 (map_iter_booker e2 bs 0)) v2)).
      destruct m ; [rewrite H5 ; auto|].
      destruct m ; [rewrite H5 ; auto|].
      unfold eq_ssubst in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0)) ; 
      destruct b ; symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))%nat = true) as LtbTrue.
      apply leb_iff ; apply leb_iff in Heqb0 ; omega.
      rewrite LtbTrue, H5 ; auto.
      rewrite H5 ; auto.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))) ; auto.
      rewrite <- StageSetProperties.ub_le_1 ; auto.
      intros ; apply CalculusProperties.svalueb_iff in Heqb.
      rewrite MP.ssubst_eassign ; destruct H4.
      destruct m ; [rewrite H7 ; auto|].
      destruct m ; [rewrite H7 ; auto|].
      unfold eq_ssubst in H7.
      rewrite EqNth in H7 ; rewrite H7 ; auto.

      (* Case not svalue 0 e1 *)
      destruct H ; apply max_lub_lt_iff in H ; auto ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto.

      rewrite MP.ssubst_bind with (f2:=(fun v1 : T.expr => bind e0 (fun v2 : T.expr => cast_eassign v1 v2))).
      destruct m ; [rewrite H3 ; auto|].
      destruct m ; [rewrite H3 ; auto|].
      unfold eq_ssubst in H3.
      rewrite EqNth in H3 ; rewrite H3 ; auto.
      intros.
      rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr => cast_eassign (ssubst m
        match m with
        | 0 => ss
        | 1 => ss
        | S (S n) =>
            if ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))
            then StageSet.add (S n) ss
            else ss
        end (cast_var (hole_var h)) v2 v) v0)).
      destruct m ; [rewrite H5 ; auto |].
      destruct m ; [rewrite H5 ; auto |].
      unfold eq_ssubst in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0)) ; destruct b ;
      symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) = true) as LtbTrue.
      apply leb_iff ; apply leb_iff in Heqb0 ; omega.
      rewrite LtbTrue, H5 ; auto.
      rewrite H5 ; auto.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))) ; auto.
      rewrite <- StageSetProperties.ub_le_1 ; auto.
      intros ; rewrite MP.ssubst_eassign ; auto.

      destruct H ; apply max_lub_lt_iff in H ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto.
      destruct H5 ; destruct H3.
      apply EqMerge ; auto.
      split ; auto.
      apply max_lub_iff ; omega.
      inversion H0.

    (* EBox *)
    specialize (IHe (0::bs) h v) ;
    specialize (booker_length e (0::bs)) ; intros BKLength.
    specialize (depth_length e (0::bs)) ; intros DpthLength1.
    specialize (eq_ssubst_fill_gt_1 e bs) ; intros EqFill1.
    specialize (eq_ssubst_fill_gt_2 e bs) ; intros EqFill2.
    destruct (trans e) ; intros.
    destruct t ; simpl in *|-* ; intros.

      (* depth e = 0 *)
      unfold eq_ssubst ; repeat(split) ; intros.

      rewrite MP.ssubst_ret, MP.ssubst_ebox ;
      rewrite DpthLength1 in *|-* ;
      rewrite BKLength in *|-* ; simpl in *|-* ;
      destruct IHe with (m:=S m) ; auto ; try(omega).
      unfold eq_ssubst in H1 ; simpl in H1 ;
      destruct m ; rewrite H1 ; auto ; [
      rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto | ] ;
      destruct m ; auto ; destruct (ltb h (nth 0 bs 0 + 0)) ; auto ;
      try(rewrite StageSetProperties.ub_le_2 with (m:=1) ; auto ; omega) ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto) ;
      try(apply StageSetProperties.ub_le_2 with (m:=(S (S m))) ; auto).

      constructor.

      rewrite MP.ssubst_ebox ;
      rewrite DpthLength1 in *|-* ;
      rewrite BKLength in *|-* ; simpl in *|-* ;
      destruct IHe with (m:=S m) ; auto ; try(omega) ;
      unfold eq_ssubst in H2 ; simpl in H2 ;
      destruct m ; rewrite H2 ; auto ; [
      rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto | ] ;
      destruct m ; auto ; destruct (ltb h (nth 0 bs 0 + 0)) ; auto ;
      try(rewrite StageSetProperties.ub_le_2 with (m:=1) ; auto ; omega) ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto) ;
      try(apply StageSetProperties.ub_le_2 with (m:=(S (S m))) ; auto).


      (* depth e > 0 *)
      rewrite DpthLength1 in H.
      destruct IHe with (m:=S m) ; auto ; try(omega).
      repeat(split) ; intros ; simpl in *|-*.
      destruct H1 ; clear H2 IHe.
      rewrite BKLength ; rewrite BKLength in H0.
      inversion H1 ; subst ; simpl in *|-*.
      
      specialize (EqFill1 h v).
      destruct t ; [contradiction|].
      apply EqFill1 ; auto.

      specialize (EqFill2 h v).
      destruct t ; [contradiction|].
      apply EqFill2 ; auto.
      
      destruct H1 ; inversion H1 ; subst ; auto ; constructor.
      inversion H2 ; subst.
      apply CalculusProperties.depth_svalue in H5 ; exfalso ; omega.
    
    (* EUnbox *)
    destruct bs ; simpl in *|-*.
    specialize (IHe nil h v) ; destruct (trans e).
    intros ; destruct m ; exfalso ; omega.

    specialize (IHe bs h v).
    specialize (context_stack_not_nil e bs) ; intros CSNotNil.
    specialize (depth_length e bs) ; intros DpthLength.
    specialize (booker_length e bs) ; intros BKLength.
    destruct (trans e) ; intros.
    destruct m ; [exfalso ; omega| simpl in *|-*].

    unfold eq_ssubst ; repeat(split) ; intros ; simpl in *|-*.
    rewrite MP.ssubst_eunbox, MP.ssubst_evar.
    destruct m ; auto ; simpl in *|-*.
    assert(beq_nat (hole_var h) (hole_var n) = false) as BeqFalse1.
    apply beq_nat_false_iff ; unfold hole_var ; omega.
    rewrite BeqFalse1 ; simpl ; constructor.

    remember (ltb h (n + 1)).
    destruct b ; symmetry in Heqb ; unfold ltb in Heqb.
    assert(CRaw.BindingSet.rho (S m)
           (StageSet.remove (S (S m)) (StageSet.add (S m) ss)) = false) as RhoFalse.
    rewrite BindingSetProperties.rho_false_mem ; auto.
    rewrite StageSetProperties.remove_mem_1 ; auto.
    apply StageSetProperties.add_mem_3 ; auto.
    rewrite RhoFalse ; simpl ; rewrite andb_false_r ; constructor.
    apply leb_iff_conv in Heqb.
    assert(beq_nat (hole_var h) (hole_var n) = false) as BeqFalse1.
    apply beq_nat_false_iff ; unfold hole_var ; omega.
    rewrite BeqFalse1 ; simpl ; constructor. 

    destruct IHe with (m:=m) ; auto ; try(omega).
    destruct bs ; simpl in *|-*.
    exfalso ; omega.
    destruct t ; simpl.
    assert((e0, n) = (e0, (n+length(tl ((e0, n) :: nil)))%nat)) as Eq1.
    rewrite plus_0_r ; auto.
    simpl tl in Eq1.
    rewrite Eq1 ; clear Eq1.
    constructor ; auto.
    rewrite BKLength in H0 ; simpl in H0.
    repeat(constructor ; auto).
    constructor ; auto.
    assert((e0, n) = (e0, (n+length(tl ((e0, n) :: nil)))%nat)) as Eq1.
    rewrite plus_0_r ; auto.
    simpl tl in Eq1.
    rewrite Eq1 ; clear Eq1.
    constructor ; auto.
    rewrite BKLength in H0 ; simpl in H0 ; auto.
    constructor.
    destruct H1 ; auto.
    inversion H0.

    (* ERun *)
    specialize (IHe bs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_erun v0)) ; 
    intros.
    rewrite H1 ; auto.
    rewrite MP.ssubst_erun ; reflexivity.
    destruct H1 ; auto.
    inversion H0.

    (* ELift *)
    specialize (IHe bs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_elift v0)) ; 
    intros.
    rewrite H1 ; auto.
    rewrite MP.ssubst_elift ; reflexivity.
    destruct H1 ; auto.
    inversion H0.
  Qed.

  Lemma eq_ssubst_2_ge:
    forall (e:S.expr) (bs:list nat) (h:S.var) (v:T.expr),
    let n := depth e in
    let (e0, cs) := trans e bs in
    forall (m:nat), 
    n <= m < length bs ->
    eq_ssubst_2 m h (booker e 0) v (nth 0 bs 0) e0 e0 /\
    eq_stack_ssubst_2 (pred m) h v 
                       (List.tl bs) (List.hd 0 bs) cs cs /\
    (svalue 0 e -> eq_ssubst_2 m h (booker e 0) v (nth 0 bs 0) (phi e bs) (phi e bs)).
  Proof.
    assert(forall (h v:nat), beq_nat (hole_var h) (source_var v) = false) as BeqFalse.
      intros ; apply beq_nat_false_iff ; unfold hole_var, source_var ; omega.

    induction e ; simpl ; intros.

    (* EConst *)
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    [rewrite MP.ssubst_ret | constructor |] ; 
    rewrite MP.ssubst_econst ; auto.

    
    (* EVar *)
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    [rewrite MP.ssubst_ret | constructor |] ;
    rewrite MP.ssubst_evar, BeqFalse ; auto.

    (* EAbs *)
    specialize (IHe bs h v0) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ; [
    rewrite MP.ssubst_ret, MP.ssubst_eabs, BeqFalse, H1 |
    destruct H1 | rewrite MP.ssubst_eabs, BeqFalse, H2 ] ; auto.

    (* EFix *)
    specialize (IHe bs h v1) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ; [
    rewrite MP.ssubst_ret, MP.ssubst_efix, BeqFalse, BeqFalse ; simpl ; rewrite H1 |
    destruct H1 | rewrite MP.ssubst_efix, BeqFalse, BeqFalse ; simpl ; rewrite H2 ] ; auto.
    
    (* EApp *)
    specialize (eq_ssubst_2_merge e1 e2 bs h v) ; intros EqMerge.
    specialize (IHe1 (map_iter_booker e2 bs 0) h v) ;
    specialize (IHe2 bs h v) ;
    destruct (trans e1) ; destruct (trans e2) ; intros.
    unfold eq_ssubst_2 ; repeat(split) ; intros.
    assert(nth 0 (map_iter_booker e2 bs 0) 0 + booker e1 0 =
     nth 0 bs 0 + (booker e1 0 + booker e2 0))%nat as EqNth.
     unfold map_iter_booker.
     specialize (List2Properties.map_iter_nth_indep 
      (fun b n : nat => (b + booker e2 n)%nat) bs 0 0 0) ; intros Prop1.
      rewrite Prop1 ; auto ; simpl ; omega.
     remember (CRaw.svalueb 0 e1) ; destruct b ; symmetry in Heqb.
    
      (* Case svalue 0 e1 *)
      destruct H ; apply max_lub_iff in H ; auto ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto.
      rewrite MP.ssubst_bind with (f2:=(fun v2 : T.expr => cast_eapp (phi e1 (map_iter_booker e2 bs 0)) v2)).
      destruct m ; [rewrite H5 ; auto|].
      unfold eq_ssubst_2 in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0)) ; 
      destruct b ; symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))%nat = true) as LtbTrue.
      apply leb_iff ; apply leb_iff in Heqb0 ; omega.
      rewrite LtbTrue, H5 ; auto.
      rewrite H5 ; auto.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))) ; auto.
      rewrite <- StageSetProperties.ub_le_1 ; auto.
      intros ; apply CalculusProperties.svalueb_iff in Heqb.
      rewrite MP.ssubst_eapp ; destruct H4.
      destruct m ; [rewrite H7 ; auto|].
      unfold eq_ssubst_2 in H7.
      rewrite EqNth in H7 ; rewrite H7 ; auto.

      (* Case not svalue 0 e1 *)
      destruct H ; apply max_lub_iff in H ; auto ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto.

      rewrite MP.ssubst_bind with (f2:=(fun v1 : T.expr => bind e0 (fun v2 : T.expr => cast_eapp v1 v2))).
      destruct m ; [rewrite H3 ; auto|].
      unfold eq_ssubst_2 in H3.
      rewrite EqNth in H3 ; rewrite H3 ; auto.
      intros.
      rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr => cast_eapp (ssubst m
        match m with
        | 0 => ss
        | S n =>
            if ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))
            then StageSet.add n ss
            else ss
        end (cast_var (hole_var h)) v2 v) v0)).
      destruct m ; [rewrite H5 ; auto |].
      unfold eq_ssubst_2 in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0)) ; destruct b ;
      symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) = true) as LtbTrue.
      apply leb_iff ; apply leb_iff in Heqb0 ; omega.
      rewrite LtbTrue, H5 ; auto.
      rewrite H5 ; auto.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))) ; auto.
      rewrite <- StageSetProperties.ub_le_1 ; auto.
      intros ; rewrite MP.ssubst_eapp ; auto.

      destruct H ; apply max_lub_iff in H ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto.
      destruct H5 ; destruct H3 ; clear H2 H4 H6 H7 IHe1 IHe2.
      apply EqMerge ; auto.
      split ; auto.
      apply max_lub_iff ; omega.
      inversion H0.

    (* ELoc *)
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    [rewrite MP.ssubst_ret | constructor |] ; 
    rewrite MP.ssubst_eloc ; auto.

    (* ERef *)
    specialize (IHe bs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_eref v0)) ; 
    intros.
    rewrite H1 ; auto.
    rewrite MP.ssubst_eref ; reflexivity.
    destruct H1 ; auto.
    inversion H0.

    (* EDeref *)
    specialize (IHe bs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_ederef v0)) ; 
    intros.
    rewrite H1 ; auto.
    rewrite MP.ssubst_ederef ; reflexivity.
    destruct H1 ; auto.
    inversion H0.

    (* EAssign *)
    specialize (eq_ssubst_2_merge e1 e2 bs h v) ; intros EqMerge.
    specialize (IHe1 (map_iter_booker e2 bs 0) h v) ;
    specialize (IHe2 bs h v) ;
    destruct (trans e1) ; destruct (trans e2) ; intros.
    unfold eq_ssubst_2 ; repeat(split) ; intros.
    assert(nth 0 (map_iter_booker e2 bs 0) 0 + booker e1 0 =
     nth 0 bs 0 + (booker e1 0 + booker e2 0))%nat as EqNth.
     unfold map_iter_booker.
     specialize (List2Properties.map_iter_nth_indep 
      (fun b n : nat => (b + booker e2 n)%nat) bs 0 0 0) ; intros Prop1.
      rewrite Prop1 ; auto ; simpl ; omega.
     remember (CRaw.svalueb 0 e1) ; destruct b ; symmetry in Heqb.
    
      (* Case svalue 0 e1 *)
      destruct H ; apply max_lub_iff in H ; auto ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto.
      rewrite MP.ssubst_bind with (f2:=(fun v2 : T.expr => cast_eassign (phi e1 (map_iter_booker e2 bs 0)) v2)).
      destruct m ; [rewrite H5 ; auto|].
      unfold eq_ssubst_2 in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0)) ; 
      destruct b ; symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))%nat = true) as LtbTrue.
      apply leb_iff ; apply leb_iff in Heqb0 ; omega.
      rewrite LtbTrue, H5 ; auto.
      rewrite H5 ; auto.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))) ; auto.
      rewrite <- StageSetProperties.ub_le_1 ; auto.
      intros ; apply CalculusProperties.svalueb_iff in Heqb.
      rewrite MP.ssubst_eassign ; destruct H4.
      destruct m ; [rewrite H7 ; auto|].
      unfold eq_ssubst_2 in H7.
      rewrite EqNth in H7 ; rewrite H7 ; auto.

      (* Case not svalue 0 e1 *)
      destruct H ; apply max_lub_iff in H ; auto ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto.

      rewrite MP.ssubst_bind with (f2:=(fun v1 : T.expr => bind e0 (fun v2 : T.expr => cast_eassign v1 v2))).
      destruct m ; [rewrite H3 ; auto|].
      unfold eq_ssubst_2 in H3.
      rewrite EqNth in H3 ; rewrite H3 ; auto.
      intros.
      rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr => cast_eassign (ssubst m
        match m with
        | 0 => ss
        | S n =>
            if ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))
            then StageSet.add n ss
            else ss
        end (cast_var (hole_var h)) v2 v) v0)).
      destruct m ; [rewrite H5 ; auto |].
      unfold eq_ssubst_2 in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0)) ; destruct b ;
      symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) = true) as LtbTrue.
      apply leb_iff ; apply leb_iff in Heqb0 ; omega.
      rewrite LtbTrue, H5 ; auto.
      rewrite H5 ; auto.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))) ; auto.
      rewrite <- StageSetProperties.ub_le_1 ; auto.
      intros ; rewrite MP.ssubst_eassign ; auto.

      destruct H ; apply max_lub_iff in H ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto.
      destruct H5 ; destruct H3.
      apply EqMerge ; auto.
      split ; auto.
      apply max_lub_iff ; omega.
      inversion H0.

    (* EBox *)
    specialize (IHe (0::bs) h v) ;
    specialize (booker_length e (0::bs)) ; intros BKLength.
    specialize (depth_length e (0::bs)) ; intros DpthLength1.
    specialize (eq_ssubst_2_fill_ge_1 e bs) ; intros EqFill1.
    specialize (eq_ssubst_2_fill_ge_2 e bs) ; intros EqFill2.
    destruct (trans e) ; intros.
    destruct t ; simpl in *|-* ; intros.

      (* depth e = 0 *)
      unfold eq_ssubst_2 ; repeat(split) ; intros.

      rewrite MP.ssubst_ret, MP.ssubst_ebox ;
      rewrite DpthLength1 in *|-* ;
      rewrite BKLength in *|-* ; simpl in *|-* ;
      destruct IHe with (m:=S m) ; auto ; try(omega).
      unfold eq_ssubst_2 in H1 ; simpl in H1 ;
      destruct m ; rewrite H1 ; auto ; [
      rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto | ] ;
      destruct m ; auto ; destruct (ltb h (nth 0 bs 0 + 0)) ; auto ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto) ;
      try(apply StageSetProperties.ub_le_2 with (m:=(S (S m))) ; auto) ;
      try(rewrite StageSetProperties.ub_le_2 with (m:=1) ; auto ; omega).

      constructor.

      rewrite MP.ssubst_ebox ;
      rewrite DpthLength1 in *|-* ;
      rewrite BKLength in *|-* ; simpl in *|-* ;
      destruct IHe with (m:=S m) ; auto ; try(omega) ;
      unfold eq_ssubst_2 in H2 ; simpl in H2 ;
      destruct m ; rewrite H2 ; auto ; [
      rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto | ] ;
      destruct m ; auto ; destruct (ltb h (nth 0 bs 0 + 0)) ; auto ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto) ;
      try(apply StageSetProperties.ub_le_2 with (m:=(S (S m))) ; auto) ;
      try(rewrite StageSetProperties.ub_le_2 with (m:=1) ; auto ; omega).
      

      (* depth e > 0 *)
      rewrite DpthLength1 in H.
      destruct IHe with (m:=S m) ; auto ; try(omega).
      repeat(split) ; intros ; simpl in *|-*.
      destruct H1 ; clear H2 IHe.
      rewrite BKLength ; rewrite BKLength in H0.
      inversion H1 ; subst ; simpl in *|-*.
      
      specialize (EqFill1 h v).
      destruct t ; [contradiction|].
      apply EqFill1 ; auto.

      specialize (EqFill2 h v).
      destruct t ; [contradiction|].
      apply EqFill2 ; auto.
      
      destruct H1 ; inversion H1 ; subst ; auto ; constructor.
      inversion H2 ; subst.
      apply CalculusProperties.depth_svalue in H5 ; exfalso ; omega.

    (* EUnbox *)
    destruct bs ; simpl in *|-*.
    specialize (IHe nil h v) ; destruct (trans e).
    intros ; destruct m ; exfalso ; omega.

    specialize (IHe bs h v).
    specialize (context_stack_not_nil e bs) ; intros CSNotNil.
    specialize (depth_length e bs) ; intros DpthLength.
    specialize (booker_length e bs) ; intros BKLength.
    destruct (trans e) ; intros.
    destruct m ; [exfalso ; omega| simpl in *|-*].

    unfold eq_ssubst_2 ; repeat(split) ; intros ; simpl in *|-*.
    rewrite MP.ssubst_eunbox, MP.ssubst_evar.

    remember (ltb h (n + 1)).
    destruct b ; symmetry in Heqb ; unfold ltb in Heqb.
    assert(CRaw.BindingSet.rho m
           (StageSet.remove (S m) (StageSet.add m ss)) = false) as RhoFalse.
    rewrite BindingSetProperties.rho_false_mem ; auto.
    rewrite StageSetProperties.remove_mem_1 ; auto.
    apply StageSetProperties.add_mem_3 ; auto.
    simpl ; rewrite RhoFalse ; simpl ; rewrite andb_false_r ; constructor.
    apply leb_iff_conv in Heqb.
    assert(beq_nat (hole_var h) (hole_var n) = false) as BeqFalse1.
    apply beq_nat_false_iff ; unfold hole_var ; omega.
    rewrite BeqFalse1 ; simpl ; constructor. 

    destruct IHe with (m:=m) ; auto ; try(omega).
    destruct bs ; simpl in *|-*.
    exfalso ; omega.
    destruct t ; simpl.
    assert((e0, n) = (e0, (n+length(tl ((e0, n) :: nil)))%nat)) as Eq1.
    rewrite plus_0_r ; auto.
    simpl tl in Eq1.
    rewrite Eq1 ; clear Eq1.
    constructor ; auto.
    rewrite BKLength in H0 ; simpl in H0.
    repeat(constructor ; auto).
    constructor ; auto.
    assert((e0, n) = (e0, (n+length(tl ((e0, n) :: nil)))%nat)) as Eq1.
    rewrite plus_0_r ; auto.
    simpl tl in Eq1.
    rewrite Eq1 ; clear Eq1.
    constructor ; auto.
    rewrite BKLength in H0 ; simpl in H0 ; auto.
    constructor.
    destruct H1 ; auto.
    inversion H0.

    (* ERun *)
    specialize (IHe bs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_erun v0)) ; 
    intros.
    rewrite H1 ; auto.
    rewrite MP.ssubst_erun ; reflexivity.
    destruct H1 ; auto.
    inversion H0.

    (* ELift *)
    specialize (IHe bs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_elift v0)) ; 
    intros.
    rewrite H1 ; auto.
    rewrite MP.ssubst_elift ; reflexivity.
    destruct H1 ; auto.
    inversion H0.
  Qed.

  Lemma eq_ssubst_eq:
    forall (e:S.expr) (bs:list nat) (h:S.var) (v:T.expr),
    let n := depth e in
    let (e0, cs) := trans e bs in
    0 < n < length bs ->
    nth (pred n) bs 0 + booker e (pred n) <= h ->
    eq_ssubst n h (booker e 0) v (nth 0 bs 0) e0 e0 /\
    eq_stack_ssubst (pred n) h v 
                       (List.tl bs) (List.hd 0 bs) cs cs /\
    (svalue 0 e -> eq_ssubst n h (booker e 0) v (nth 0 bs 0) (phi e bs) (phi e bs)).
  Proof.
    intros ; subst n.
    specialize (booker_length e bs) ; intros BKLength.
    specialize (depth_length e bs) ; intros DpthLength.
    specialize (eq_ssubst_2_ge e bs) ; intros Strong.
    destruct (trans e) ; intros.
    specialize (Strong h v (depth e)) ; simpl in Strong.
    destruct Strong ; auto ; try(omega).
    destruct H2.
    rewrite BKLength in *|-*.

    repeat(split ; intros).

    (* Part 1 *)
    unfold eq_ssubst ; unfold eq_ssubst_2 in H1 ; intros.
    destruct (depth e) ; [exfalso ; omega|].
    destruct n ; auto ; simpl in *|-*.
    assert(ltb h (nth 0 bs 0 + length (nth 0 t nil)) = false) as False1.
    apply leb_iff_conv ; omega.
    rewrite False1 in H1 ; auto.

    (* Part 2 *)
    rewrite DpthLength in *|-*.
    clear BKLength DpthLength H1 H3.
    generalize dependent bs.
    induction t ; simpl in *|-* ; intros.
    constructor.
    destruct bs ; simpl in *|-* ; [exfalso; omega|].
    inversion H2 ; subst ;
    constructor ; simpl in *|-* ; auto.

    clear IHt H2.
    induction a.
    constructor.
    inversion H5 ; subst ; simpl in *|-* ; auto.
    constructor ; auto.
    apply IHa ; auto ; omega.
    

    clear IHt H2 H10.
    induction a.
    constructor.
    inversion H7 ; subst ; simpl in *|-* ; auto.
    constructor ; auto.
    unfold eq_ssubst ; unfold eq_ssubst_2 in H4 ; intros.
    destruct (length cs1) ; auto.
    assert(ltb h (b1 + length c1') = false) as False1.
    apply leb_iff_conv ; omega.
    rewrite False1 in H4 ; auto.

    specialize (IHt (b1::bs0)).
    simpl in IHt ; apply IHt ; auto.
    omega.

    (* Part 3 *)
    unfold eq_ssubst ; unfold eq_ssubst_2 in H3 ; intros.
    specialize (H3 H4).
    destruct (depth e) ; [exfalso ; omega|].
    destruct n ; auto ; simpl in *|-*.
    assert(ltb h (nth 0 bs 0 + length (nth 0 t nil)) = false) as False1.
    apply leb_iff_conv ; omega.
    rewrite False1 in H3 ; auto.
  Qed.

  Lemma eq_ssubst_admin:
    forall (e:T.expr) (b m n:nat) (h:S.var) (v:T.expr),
    eq_ssubst n h m v b e e ->
    admin_ssubst n h m v b e e.
  Proof.
    intros ; unfold admin_ssubst ; intros.
    rewrite H ; auto.
    constructor.
  Qed.

  Lemma eq_context_ssubst_admin:
    forall (c:Context.t) (b1 b2 m n:nat) (h:S.var) (v:T.expr),
    eq_context_ssubst n h m v b1 b2 c c ->
    admin_context_ssubst n h m v b1 b2 c c.
  Proof.
    induction c ; intros.
    constructor.
    inversion H ; subst ; constructor.
    apply eq_ssubst_admin ; auto.
    apply IHc ; auto.
  Qed.

  Lemma eq_stack_ssubst_admin:
    forall (cs:Context.t_stack) (bs:list nat) (b n:nat) (h:S.var) (v:T.expr),
    eq_stack_ssubst n h v bs b cs cs ->
    admin_stack_ssubst n h v bs b cs cs.
  Proof.
    induction cs ; intros.
    constructor.
    inversion H ; subst ; constructor.
    apply eq_context_ssubst_admin ; auto.
    apply eq_context_ssubst_admin ; auto.
    apply IHcs ; auto.
  Qed.

  Lemma map_iter_stack_nil:
    forall (bs:list nat) (n:nat),
    map_iter_stack nil bs n = bs.
  Proof.
    induction bs ; simpl ; intros ; auto.
    unfold map_iter_stack in *|-* ; simpl ;
    rewrite IHbs ; destruct n ; rewrite plus_0_r ; reflexivity.
  Qed.

  Lemma map_iter_stack_cons:
    forall (bs:list nat) (c:Context.t) (cs:Context.t_stack) (n:nat),
    map_iter_stack (c::cs) bs (S n) = map_iter_stack cs bs n.
  Proof.
    induction bs ; simpl ; intros ; auto.
    unfold map_iter_stack in *|-* ; simpl in *|-*.
    rewrite IHbs ; destruct n ; reflexivity.
  Qed.

  Lemma map_iter_stack_nth:
    forall (bs:list nat) (cs:Context.t_stack)  (b:nat) (n:nat),
    map_iter_stack cs (b :: bs) n = 
    (b + length (nth n cs nil))%nat :: map_iter_stack cs bs (S n).
  Proof.
    induction bs ; simpl ; intros ; auto.
  Qed.

  Lemma admin_ssubst_m_Sm:
    forall (e1 e2:T.expr) (b:nat) (h:S.var) (v:T.expr) (n m:nat),
    admin_ssubst n h m v b e1 e2 -> admin_ssubst n h (S m) v b e1 e2.
  Proof.
    unfold admin_ssubst ; intros.
    case_beq_nat h (b + m)%nat.
    assert(ltb (b+m)%nat (b + m)%nat = false) as LtbFalse.
    apply leb_iff_conv ; omega.
    rewrite LtbFalse in H.
    assert(ltb (b+m)%nat (b + S m)%nat = true) as LtbTrue.
    apply leb_iff ; omega.
    rewrite LtbTrue.
    destruct n.
    apply H ; auto.
    destruct n.
    apply H ; auto.
    apply H ; auto.
    rewrite StageSetProperties.add_mem_4 ; auto.
    rewrite <- StageSetProperties.ub_le_1 ; auto.
    assert(ltb h (b + S m) = ltb h (b + m)) as Eq1.
    generalize E ; clear ; intros.
    remember (ltb h (b + m)) ; destruct b0 ; symmetry in Heqb0 ;
    [apply leb_iff ; apply leb_iff in Heqb0 | 
    apply leb_iff_conv ; apply leb_iff_conv in Heqb0] ; omega.
    rewrite Eq1 ; apply H ; auto.
  Qed.

  Lemma admin_ssubst_m_ge:
    forall (e1 e2:T.expr) (b:nat) (h:S.var) (v:T.expr) (n m p:nat),
    admin_ssubst n h m v b e1 e2 -> 
    m <= p -> admin_ssubst n h p v b e1 e2.
  Proof.
    intros.
    induction H0 ; auto.
    apply admin_ssubst_m_Sm ; auto.
  Qed.

  Lemma admin_context_ssubst_m_ge:
    forall (c1 c2:Context.t) (b1 b2:nat) (h:S.var) (v:T.expr) (n m p:nat),
    admin_context_ssubst n h m v b1 b2 c1 c2 -> 
    m <= p -> admin_context_ssubst n h p v b1 b2 c1 c2.
  Proof.
    induction c1 ; intros ; inversion H ; subst ;
    constructor ; auto.
    apply admin_ssubst_m_ge with (m:=m) ; auto.
    apply IHc1 with (m:=m) ; auto.
  Qed.

  Lemma admin_ssubst_sum:
    forall (e1 e2 v:T.expr) (n m1 m2 b1 b2:nat) (h:S.var),
    admin_ssubst n h m1 v b1 e1 e2 ->
    (b1 + m1 = b2 + m2)%nat ->
    admin_ssubst n h m2 v b2 e1 e2.
  Proof.
    unfold admin_ssubst ; intros.
    rewrite <- H0.
    apply H ; auto.
  Qed.

  Lemma admin_context_ssubst_sum:
    forall (c1 c2:Context.t) (v:T.expr) (n m1 m2 b1 b2 b3:nat) (h:S.var),
    admin_context_ssubst n h m1 v b1 b3 c1 c2 ->
    (b1 + m1 = b2 + m2)%nat ->
    admin_context_ssubst n h m2 v b2 b3 c1 c2.
  Proof.
    induction c1 ; simpl ; intros ;
    inversion H ; subst ;
    constructor ; auto.
    apply admin_ssubst_sum with (m1:=m1) (b1:=b1) ; auto.
    apply IHc1 with (m1:=m1) (b1:=b1) ; auto.
  Qed.

(*
  Lemma admin_stack_ssubst_app:
    forall (cs1 cs2 cs3 cs4:Context.t_stack) (bs:list nat) (m n b:nat) (h:S.var) (v:T.expr),
    admin_stack_ssubst n h v bs b cs1 cs3 ->
    admin_stack_ssubst n h v bs b cs2 cs4 ->
    admin_stack_ssubst n h v bs b (cs1 ++ cs2) (cs3 ++ cs4).
  Proof.
    induction cs1 ; simpl ; intros ;
    inversion H ; subst ; simpl ; auto.
    inversion H0 ; subst.
    constructor ; auto.
    constructor ; auto.
    apply admin_context_ssubst_m_ge with (m:=0) ; auto ; omega.

    simpl ; auto.
    assert((b2 + length c2 + length c1) = b2 + (length (c1++c2)))%nat as Eq1.
    rewrite app_length ; simpl ; omega.
    rewrite Eq1 ; constructor ; auto.
  Qed.*)

  Lemma merge_unshift_1:
    forall (cs1 cs2:Context.t_stack) (c:Context.t),
    length cs2 <= length cs1 ->
    Context.unshift (Context.merge cs1 cs2) c = 
    Context.merge (Context.unshift cs1 c) cs2.
  Proof.
    induction cs1 ; intros.
    destruct cs2 ; [|exfalso ; simpl in *|-* ; omega].
    simpl ; auto.
    destruct cs2.
    simpl ; auto.
    simpl.
    rewrite IHcs1 ; auto.
    simpl in *|-* ; omega.
  Qed.

  Lemma admin_stack_ssubst_merge_2:
    forall (bs:list nat) (e1 e2 e3:S.expr), 
    let (e1', cs1) := trans e1 (map_iter_booker e2 bs 0) in
    let (e2', cs2) := trans e2 bs in
    let (e3', cs3) := trans e3 (map_iter_booker e2 bs 0) in
    match cs1 with
    | nil => True
    | _ => let (c1, cs1') := Context.shift cs1 in
      match c1 with
      | nil => True
      | cons (t_eh, h) c1' => 
        forall (eh:S.expr),
        t_eh = trans_expr eh (0::nil) ->
        match c1' with
        | nil =>
            admin_stack_ssubst (pred (depth e1)) h (phi eh (0 :: nil))
            (tl (map_iter_booker e2 bs 0))
            (hd 0 (map_iter_booker e2 bs 0)) cs1' cs3
        | _ :: _ =>
            admin_stack_ssubst (pred (depth e1)) h (phi eh (0 :: nil))
            (tl (map_iter_booker e2 bs 0))
            (hd 0 (map_iter_booker e2 bs 0)) (Context.unshift cs1' c1') cs3
        end ->
        depth e2 < depth e1 < length bs ->
        match c1' with
        | nil =>
          admin_stack_ssubst (pred (depth e1)) h (phi eh (0 :: nil)) (tl bs)
          (hd 0 bs) (Context.merge cs1' cs2)
          (Context.merge cs3 cs2)
        | _ =>
          admin_stack_ssubst (pred (depth e1)) h (phi eh (0 :: nil)) (tl bs)
          (hd 0 bs)
          (Context.unshift (Context.merge cs1' cs2) c1')
          (Context.merge cs3 cs2)
        end
      end
    end.
  Proof.
    intros.
    specialize (map_iter_booker_stack e2 bs) ; intros MapIterBooker.
    specialize (depth_length e1 (map_iter_booker e2 bs 0)) ; intros DpthLength1.
    specialize (depth_length e2 bs) ; intros DpthLength2.
    specialize (eq_ssubst_gt e2 bs) ; intros EqSsubstEq.
    destruct (trans e1).
    destruct (trans e2).
    destruct (trans e3).
    destruct t ; auto.
    assert(Context.shift (t :: t2) = Context.shift ((fun x => x) (t :: t2))) as Shift1.
    reflexivity.
    destruct (Context.shift (t :: t2)).
    destruct t3 ; auto.
    destruct p ; intros.
    specialize (EqSsubstEq v (phi eh (0 :: nil)) (depth e1) H1).
    destruct EqSsubstEq ; clear H2 ; destruct H3 ; clear H3.
    rewrite DpthLength1, DpthLength2, MapIterBooker in *|-*.
    clear H DpthLength1 DpthLength2 MapIterBooker.
    simpl in *|-*.
    destruct bs ; [exfalso ; simpl in *|-* ; omega |].
    rewrite map_iter_stack_nth in *|-*.
    simpl in *|-*.

    destruct t3.

    (* c1' nil *)
    clear Shift1.
    generalize dependent n ;
    generalize dependent t2 ; generalize dependent t1 ; 
    generalize dependent bs ; generalize dependent t0.
    induction t4 ; simpl ; intros.
    inversion H0 ; subst.
    apply eq_stack_ssubst_admin ; auto.
    destruct t1.
    inversion H0 ; subst.
    simpl.
    destruct bs ; [exfalso ; simpl in *|-* ; omega |].

    destruct t0 ; auto.
    rewrite map_iter_stack_nil in *|-* ; auto.
    simpl in *|-* ; rewrite plus_0_r in *|-* ; auto.

    (* induction case *)
    destruct t2 ; simpl in *|-* ; [exfalso ; omega|].
    assert(admin_stack_ssubst (length t6) v (phi eh (0 :: nil)) bs n0
         (Context.merge t4 t5) (Context.merge t3 t5)).
    apply IHt4 ; auto ; clear IHt4.
    omega.
    inversion H2 ; subst ; auto.
    constructor.

    rewrite map_iter_stack_nth, map_iter_stack_cons in H0 ; auto.
    inversion H0 ; subst ; auto.
    constructor.

    destruct t4.
    inversion H0 ; subst ; simpl in *|-* ; auto.
    destruct t5.
    constructor ; auto.
    apply congr_ssubst_context_app ; auto.
    rewrite plus_0_r in H6 ; auto.
    apply eq_context_ssubst_admin ; auto.
    inversion H2 ; subst ; auto.
    
    constructor ; auto.
    apply congr_ssubst_context_app ; auto.
    apply admin_context_ssubst_sum with (m1:=0) (b1:=(n0 + length t3)%nat) ;
    simpl in *|-* ; auto ; omega.
    apply eq_context_ssubst_admin ; auto.
    inversion H2 ; subst ; auto.
    
    remember (Context.merge (t4 :: t7) t5).
    destruct t8.
    simpl in Heqt8 ; destruct t5 ; inversion Heqt8.
    remember (Context.merge t3 t5).
    destruct t10.
    inversion H0 ; subst.
    simpl in Heqt10 ; destruct t5 ; inversion Heqt10.
    destruct t5 ; auto.

    rewrite ContextStaticProperties.merge_nil_r in *|-*.
    simpl in *|-* ; inversion Heqt8 ; inversion Heqt10 ; subst ; simpl in *|-*.
    constructor ; auto.
    apply congr_ssubst_context_app ; auto.
    inversion H0 ; subst.
    rewrite plus_0_r in H8 ; auto.
    apply admin_context_ssubst_m_ge with (m:=0) ; auto ; try(omega).
    apply eq_context_ssubst_admin ; auto.
    inversion H2 ; subst ; auto.
    
    constructor ; auto.
    apply congr_ssubst_context_app ; auto.
    inversion H0 ; subst.
    clear H12 H0.
    apply admin_context_ssubst_sum with (m1:=length t4) (b1:=(n0 + (length t5))%nat) ;
    auto.
    simpl in Heqt8 ; inversion Heqt8 ; rewrite app_length ; omega.
    apply admin_context_ssubst_m_ge with (m:=length t5) ; auto ; try(omega).
    apply eq_context_ssubst_admin ; auto.
    inversion H2 ; subst ; auto.
    simpl in Heqt8 ; inversion Heqt8 ; rewrite app_length ; omega.

    (* c1' not nil *)
    rewrite merge_unshift_1 ; auto.
    clear Shift1.
    rewrite ContextStaticProperties.unshift_spec in *|-*.
    generalize dependent n ;
    generalize dependent t2 ; generalize dependent t1 ; 
    generalize dependent bs ; generalize dependent t0.
    induction t4 ; simpl ; intros.
    inversion H0 ; subst.
    destruct t0 ; auto.

    rewrite map_iter_stack_nil in *|-* ; subst ; auto.
    simpl in *|-* ; rewrite plus_0_r in *|-* ; auto.

    simpl in *|-*.
    rewrite map_iter_stack_cons in *|-*.
    inversion H2 ; subst.
    simpl.
    constructor ; auto.
    rewrite map_iter_stack_nil in *|-* ; subst ; auto.
    inversion H ; subst ; auto.
    rewrite app_comm_cons.
    apply congr_ssubst_context_app ; auto.
    apply eq_context_ssubst_admin ; auto.
    constructor ; auto.
    rewrite map_iter_stack_nth, map_iter_stack_cons in *|-*.
    inversion H ; subst ; auto.
    rewrite app_comm_cons.
    apply congr_ssubst_context_app ; auto.
    apply admin_context_ssubst_sum with (m1:=0) (b1:=(b0 + length c1')%nat) ;
    auto ; try(omega).
    apply eq_context_ssubst_admin ; auto.
    apply eq_stack_ssubst_admin ; auto.

    destruct bs ; [exfalso ; simpl in *|-* ; omega |].
    destruct t0 ; auto.
    rewrite map_iter_stack_nil in *|-* ; auto.
    simpl in *|-* ; rewrite plus_0_r in *|-* ; auto.
    rewrite ContextStaticProperties.merge_nil_r ; auto.
    rewrite map_iter_stack_nth, map_iter_stack_cons in *|-*.
    inversion H0 ; subst.
    apply app_cons_not_nil in H7 ; contradiction.

    (* induction case *)
    destruct t2 ; [simpl in *|-* ; exfalso ; omega|].
    assert(admin_stack_ssubst (length t2) v (phi eh (0 :: nil)) bs n0
         (Context.merge (t4 ++ (p :: t3) :: nil) t5) (Context.merge (c2' :: cs2) t5)).
    apply IHt4 ; auto ; clear IHt4 ; simpl in *|-*.
    omega.
    inversion H2 ; subst ; auto.
    constructor.
    rewrite <- H7 ; auto.

    remember (Context.merge (c1' :: cs1) t5).
    destruct t6.
    simpl in Heqt6 ; destruct t5 ; inversion Heqt6.
    remember (Context.merge (c2' :: cs2) t5).
    destruct t8.
    simpl in Heqt8 ; destruct t5 ; inversion Heqt8.
    remember (c2' :: cs2) ; simpl ; subst.
    rewrite <- Heqt8.
    constructor ; auto.
    apply congr_ssubst_context_app ; auto.
    simpl in *|-* ; auto.
    apply admin_context_ssubst_sum with (m1:=length c1') (b1:=(n0 + (length (nth 0 t5 nil)))%nat) ;
    auto.
    destruct t5 ; inversion Heqt6 ; subst ; 
    try(rewrite app_length) ; simpl ; omega.
    apply admin_context_ssubst_m_ge with (m:=(length (nth 0 t5 nil))) ; auto ; try(omega).
    apply eq_context_ssubst_admin ; auto.
    inversion H2 ; subst ; auto.
    destruct t5 ; simpl in *|-* ; [omega|] ; inversion Heqt6 ; subst ; 
    simpl in *|-*.
    rewrite app_length ; omega.
    rewrite Heqt6, Heqt8, H7 in *|-* ; auto.

    (* length t0 <= length t4 *)
    specialize (ContextStaticProperties.shift_spec (t :: t2)) ; intros Spec1.
    simpl in Spec1.
    destruct (Context.shift t2).
    destruct t2.
    admit.
    inversion Shift1 ; subst.
    assert(length (t :: t2 :: t7) = length ((t :: t6) ++ ((e5, v) :: p :: t3) :: nil)) as Eq1.
    rewrite Spec1 ; simpl ; auto ; omega.
    simpl in Eq1.
    rewrite app_length in Eq1.
    simpl in *|-* ; omega.
  Qed.

  Lemma sstep_rstep:
    forall (e1:S.expr) (bs:list nat) (e2:S.expr) (M1 M2:S.Memory.t),
    S.memory_svalue 0 M1 ->
    S.memory_depth M1 = 0 ->
    let n := depth e1 in
    n < length bs ->
    S.sstep n (M1, e1) (M2, e2) -> 
    let (e1', cs1) := trans e1 bs in
    match cs1 with
    | nil => rstep (trans_mem M1 bs, e1') (trans_mem M2 bs, trans_expr e2 bs)
    | cs1 => let (c1, cs1') := Context.shift cs1 in
      match c1 with
      | nil => False
      | cons (t_eh, h) c1' => 
          let (e2', cs2) := trans e2 bs in
          let M1' := trans_mem M1 bs in
          let M2' := trans_mem M2 bs in
          exists eh, t_eh = trans_expr eh (0::nil) /\
          (
            S.svalue 0 eh /\ 
            M1 = M2 /\
            match c1' with
            | nil => admin_stack_ssubst (pred n) h (phi eh (0::nil)) 
                       (List.tl bs) (List.hd 0 bs) cs1' cs2
            | _ =>   admin_stack_ssubst (pred n) h (phi eh (0::nil))
                       (List.tl bs) (List.hd 0 bs) (Context.unshift cs1' c1') cs2
            end /\
            admin_ssubst n h (booker e1 0) (phi eh (0::nil)) (nth 0 bs 0) e1' e2' /\
            (svalue 0 e1 -> admin_ssubst n h (booker e1 0) (phi eh (0::nil)) (nth 0 bs 0) 
              (phi e1 bs) (phi e2 bs))
          \/ 
            exists eh', let t_eh' := trans_expr eh' (0::nil) in
            rstep (M1', t_eh) (M2', t_eh') /\
            e1' = e2' /\ phi e1 bs = phi e2 bs /\ 
            (forall m, m <= n -> S.CRaw.svalueb m e1 = S.CRaw.svalueb m e2) /\
            cs2 = Context.unshift cs1' ((t_eh', h) :: c1')
          )
      end
    end.
  Proof.
    induction e1 ; simpl ; 
    intros bs e2 M1 M2 MemSvalue0 MemDepth0 BSLength Step ; intros.

    (* Case EConst *)
    inversion Step.

    (* Case EVar *)
    inversion Step.

    (* Case EAbs *)
    inversion Step ; subst.
    rewrite <- H in IHe1, BSLength.
    specialize (IHe1 bs e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
    specialize (depth_length e1 bs) ; intros.
    destruct (trans e1).
    rewrite <- H in H0.
    destruct t ; simpl in H0 ; inversion H0 ; subst.
    destruct (Context.shift (t :: t0)).
    destruct t1 ; simpl in *|-* ; auto.
    destruct p ; destruct (trans e3) ; intros.
    destruct IHe1 ; exists x.
    destruct H2 ; split ; [assumption|].
    destruct H3 ; [left | right] ; destruct H3.

      (* Case svalue *)
      destruct H4 ; destruct H5 ; subst.
      repeat(split ; auto).
      unfold admin_ssubst ; intros.
      assert(beq_var (hole_var v0) (source_var v) = false).
      clear ; unfold hole_var, source_var ; apply beq_nat_false_iff ; omega.
      destruct t0 ; simpl in *|-*.
      rewrite MP.ssubst_ret, MP.ssubst_eabs.
      repeat(constructor).
      apply H6.
      rewrite H7 ; assumption.
      rewrite H7 ; assumption.
      unfold admin_ssubst in H6.
      destruct (ltb v0 (nth 0 bs 0 + booker e1 0)) ;
      rewrite MP.ssubst_ret, MP.ssubst_eabs ;
      repeat(constructor) ;
      rewrite H7 ;
      apply H6 ; auto.

      (* patch *)
      unfold admin_ssubst ; intros.
      assert(beq_var (hole_var v0) (source_var v) = false).
      clear ; unfold hole_var, source_var ; apply beq_nat_false_iff ; omega.
      destruct t0 ; simpl in *|-*.
      rewrite MP.ssubst_eabs.
      repeat(constructor).
      apply H6.
      rewrite H8 ; assumption.
      rewrite H8 ; assumption.
      unfold admin_ssubst in H6.
      destruct (ltb v0 (nth 0 bs 0 + booker e1 0)) ;
      rewrite MP.ssubst_eabs ;
      repeat(constructor) ;
      rewrite H8 ;
      apply H6 ; auto.
      

      (* Case not svalue *)
      exists x0.
      destruct H3 ; destruct H4 ; destruct H5 ; 
      destruct H6 ; subst ; auto.
      repeat(split) ; intros ; auto.
      rewrite H6 ; auto.

    (* Case EFix *)
    inversion Step ; subst.
    rewrite <- H in IHe1, BSLength.
    specialize (IHe1 bs e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
    specialize (depth_length e1 bs) ; intros.
    destruct (trans e1).
    rewrite <- H in H0.
    destruct t ; simpl in H0 ; inversion H0 ; subst.
    destruct (Context.shift (t :: t0)).
    destruct t1 ; simpl in *|-* ; auto.
    destruct p ; destruct (trans e3) ; intros.
    destruct IHe1 ; exists x.
    destruct H2 ; split ; [assumption|].
    destruct H3 ; [left | right] ; destruct H3.
    
      (* Case svalue *)
      destruct H4 ; destruct H5 ; subst.
      repeat(split ; auto).
      intros.
      unfold admin_ssubst ; intros.
      assert(beq_var (hole_var v1) (source_var v)
               || beq_var (hole_var v1) (source_var v0) = false).
      clear ; unfold hole_var, source_var ;
      apply orb_false_iff ; split ; apply beq_nat_false_iff ; omega.
      destruct t0 ; simpl in *|-*.
      rewrite MP.ssubst_ret, MP.ssubst_efix.
      repeat(constructor).
      apply H6.
      rewrite H7 ; assumption.
      rewrite H7 ; assumption.
      unfold admin_ssubst in H6.
      destruct (ltb v0 (nth 0 bs 0 + booker e1 0)) ;
      rewrite MP.ssubst_ret, MP.ssubst_efix ;
      repeat(constructor) ;
      rewrite H7 ;
      apply H6 ; auto.

      (* patch *)
      unfold admin_ssubst ; intros.
      assert(beq_var (hole_var v1) (source_var v)
               || beq_var (hole_var v1) (source_var v0) = false).
      clear ; unfold hole_var, source_var ;
      apply orb_false_iff ; split ; apply beq_nat_false_iff ; omega.
      destruct t0 ; simpl in *|-*.
      rewrite MP.ssubst_efix.
      repeat(constructor).
      apply H6.
      rewrite H8 ; assumption.
      rewrite H8 ; assumption.
      unfold admin_ssubst in H6.
      destruct (ltb v0 (nth 0 bs 0 + booker e1 0)) ;
      rewrite MP.ssubst_efix ;
      repeat(constructor) ;
      rewrite H8 ;
      apply H6 ; auto.

      (* Case not svalue *)
      exists x0.
      destruct H3 ; destruct H4 ; destruct H5 ; 
      destruct H6 ; subst ; auto.
      repeat(split) ; intros ; auto.
      rewrite H6 ; auto.


    (* Case EApp *)
    inversion Step ; subst ; simpl in *|-*.
    
      (* Case EApp e1 e2,  e1 -> e1' *)
      specialize (length_h_match e1_1 (map_iter_booker e1_2 bs 0)) ; intros LengthHMatch.
      specialize (booker_length e1_2 bs) ; intros BookerLength2.
      specialize (max_spec (depth e1_1) (depth e1_2)) ; intros MaxLeft.
      destruct MaxLeft ; destruct H.
      rewrite H0 in H1.
      specialize (CalculusProperties.depth_sstep_lt 
        M1 e1_1 M2 e3 (depth e1_2) H H1) ;
      intros ; contradiction.
      rewrite H0 in *|-* ; clear IHe1_2.
      specialize (IHe1_1 (map_iter_booker e1_2 bs 0) 
        e3 M1 M2 MemSvalue0 MemDepth0).
      assert(length (map_iter_booker e1_2 bs 0) = length bs) as Eq2.
      unfold map_iter_booker ; 
      rewrite List2Properties.length_map_iter ; auto.
      rewrite Eq2 in IHe1_1 ; specialize (IHe1_1 BSLength H1).
      specialize (depth_length e1_1 (map_iter_booker e1_2 bs 0)) ; intros DpthLength3.
      specialize (depth_length e1_2 bs) ; intros DpthLength4.
      unfold trans_expr ; simpl.
      specialize (CalculusProperties.depth_sstep_eq 
          M1 e1_1 M2 e3 MemDepth0 H1) ; intros Dpth1.
      specialize (eq_ssubst_eq e1_2 bs) ; intros EqSsubstEq1.
      specialize (eq_ssubst_gt e1_2 bs) ; intros EqSsubstEq2.
      specialize (admin_stack_ssubst_merge_2 bs e1_1 e1_2) ; intros AdminSsubst2.
      destruct (trans e1_1).
      destruct (trans e1_2).
      destruct t.
 
        (* Case EApp e1 e2, n = 0, e1 -> e1' *)
        destruct t0 ; [|exfalso ; simpl in *|-* ; omega] ; simpl.
        unfold trans_expr in IHe1_1 ; 
        assert(trans e3 (map_iter_booker e1_2 bs 0) = trans ((fun x => x) e3) (map_iter_booker e1_2 bs 0)) as Transe1.
        reflexivity.
        destruct (trans e3).
        inversion IHe1_1 ; subst.
        simpl in *|-* ; destruct Dpth1.
        assert(S.CRaw.svalueb 0 e1_1 = false).
        apply CalculusProperties.svalueb_iff_conv.
        apply CalculusProperties.sprogresses_not_svalue with (M1:=M1).
        exists (M2, e3) ; rewrite DpthLength3 in H1 ; auto.
        rewrite H4.
        remember (S.CRaw.svalueb 0 e3) ; destruct b ; symmetry in Heqb.
        apply CalculusProperties.svalueb_iff in Heqb.
        apply Rel_step with (e1:=bind e0
        (fun v2 => cast_eapp (phi e3 (map_iter_booker e1_2 bs 0)) v2)).
        specialize (MP.astep_bind_1 e3 e e2 bs (trans_mem M1 bs) (trans_mem M2 bs)
          (fun v1 : T.expr => bind e0 (fun v2 : T.expr => cast_eapp v1 v2))) ; intros.
        rewrite phi_depth_0 with (bs2:=bs) ; auto.
        apply H7 ; auto.
        rewrite trans_memory_depth_0 with (bs2:=bs) in H5 ; auto.
        rewrite trans_memory_depth_0 with (bs1:=(map_iter_booker e1_2 bs 0)) (bs2:=bs) in H5 ; auto.
        rewrite trans_depth_0 with (bs2:=bs) in Transe1 ; auto.
        specialize (svalue_phi e3 bs Heqb) ; intros.
        unfold trans_expr in H8 ; rewrite <- Transe1 in H8.
        subst ; auto.
        omega.
        omega.
        constructor.
        
        apply Rel_step with (e1:=bind e2 (fun v1 => bind e0 
          (fun v2 => cast_eapp v1 v2))).
        apply MP.astep_bind_app ; auto.
        rewrite trans_memory_depth_0 with (bs2:=bs) in H5 ; auto.
        rewrite trans_memory_depth_0 with (bs1:=(map_iter_booker e1_2 bs 0)) (bs2:=bs) in H5 ; auto.
        constructor ; auto.
        intros ; constructor.

        (* Case EApp e1 e2, n > 0, e1 -> e1' *)
        assert (Context.merge (t::t1) t0 = 
          Context.merge (t::t1) ((fun x => x) t0)) as Merge1.
          reflexivity.
        inversion H.
        
          (* Case depth(e1) = depth(e2) *)
          rewrite ContextStaticProperties.shift_merge_3 ;
          [| rewrite DpthLength4 in H3 ; rewrite DpthLength3 in H3] ; auto.
          destruct (Context.merge (t::t1) t0).
          simpl in Merge1 ; destruct t0 ; inversion Merge1.
          assert (Context.shift (t::t1) =  Context.shift ((fun x => x) (t::t1))) as Merge2.
          reflexivity.
          destruct (Context.shift (t :: t1)).
          assert (Context.shift t0 =  Context.shift ((fun x => x) t0)) as Merge3.
          reflexivity.
          destruct (Context.shift t0).
          destruct t4 ; [exfalso |] ; auto ; simpl.
          destruct p.
          specialize (svalue_phi e3 (map_iter_booker e1_2 bs 0)) ; 
          intros SValuePhi3 ; unfold trans_expr in SValuePhi3.
          destruct (trans e3).
          destruct IHe1_1.
          exists x.
          destruct H2 ; split ; auto.
          destruct H4 ; [left|right] ; destruct H4.

            (* Case svalue *)
            destruct H5 ; destruct H6.
            repeat(split) ; auto.
            admit. (* Todo: prove it. Create a separated lemma *)
            
            remember (S.CRaw.svalueb 0 e1_1).
            destruct b ; symmetry in Heqb.

              (* Case svalue 0 e1_1 *)
              apply CalculusProperties.svalueb_iff in Heqb.
              assert(svalue 0 e3) as SValueE3.
                inversion Heqb ; subst ; 
                try(inversion H1 ; constructor ; fail).
                inversion H1 ; subst ; simpl in *|-*.
                apply CalculusProperties.depth_svalue in H8.
                exfalso ; omega.
              apply CalculusProperties.svalueb_iff in SValueE3.
              rewrite SValueE3.
              unfold admin_ssubst ; intros.
              rewrite MP.ssubst_bind with (f2:=
                fun v2 => cast_eapp (
                ssubst (depth e1_2)
                 match depth e1_2 with
                 | 0 => ss
                 | 1 => ss
                 | S (S n) =>
                 if ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))
                 then StageSet.add (S n) ss
                 else ss
                 end (cast_var (hole_var v))
                 (phi e1_1 (map_iter_booker e1_2 bs 0)) (phi x (0 :: nil)))
               v2) ; auto.
               constructor ; auto.
               simpl in *|-*.
               unfold map_iter_booker in LengthHMatch.
               assert(S (length t1) <= length
                 (List2.map_iter (fun b n => (b + booker e1_2 n)%nat) bs 0)) as Tmp1.
               rewrite List2Properties.length_map_iter ; auto.
               omega.
               specialize (LengthHMatch Tmp1) ; clear Tmp1.
               unfold map_iter_booker in LengthHMatch.
               specialize (List2Properties.map_iter_nth_indep 
                 (fun b n : nat => (b + booker e1_2 n)%nat)
                 bs (length t1) 0 0 0) ; intros MapIter1.
                 rewrite MapIter1 in LengthHMatch ; auto.
               subst.
               destruct EqSsubstEq1 with (h:=(nth (length t1) bs 0 + booker e1_2 (length t1 + 0) + length t4)%nat) (v:=(phi x (0 :: nil))) ; auto.
               rewrite H3 ; split ; auto ; rewrite DpthLength3 ; omega.
               rewrite H3, DpthLength3, plus_0_r ; simpl ; omega.
               unfold eq_ssubst in H2.
               remember (ltb
                (nth (length t1) bs 0 + booker e1_2 (length t1 + 0) +
                 length t4) (nth 0 bs 0 + booker e1_2 0)).
               destruct b ; symmetry in Heqb0.
               assert(ltb (nth (length t1) bs 0 + booker e1_2 (length t1 + 0) + length t4)
               (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0)) = true) as True1.
                 apply leb_iff ; apply leb_iff in Heqb0 ; rewrite plus_0_r in *|-* ; omega.
               rewrite True1, H2 ; auto ; try(omega) ; constructor.
               destruct (depth e1_2) ; try(rewrite H2 ; auto ; try(omega) ; constructor).
               destruct n ; try(rewrite H2 ; auto ; try(omega) ; constructor).
               rewrite H2 ; auto ; try(omega) ; [constructor |].
               destruct (ltb (nth (length t1) bs 0 + booker e1_2 (length t1 + 0) + length t4)
                 (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))) ; auto.
               rewrite <- StageSetProperties.ub_le_1 ; auto.
               omega.
               intros.
               constructor ; [|constructor].
               destruct H7.
               specialize (H10 Heqb).
               unfold admin_ssubst in H10.
               assert((nth 0 (map_iter_booker e1_2 bs 0) 0 + booker e1_1 0)%nat
               = (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))%nat) as Nth1.
                 specialize (List2Properties.map_iter_nth_indep 
                   (fun b n : nat => (b + booker e1_2 n)%nat)
                   bs 0 0 0 0) ; intros MapIter1.
                 unfold map_iter_booker ; rewrite MapIter1.
                 simpl ; clear ; omega.
                 destruct (depth e1_1) ; omega.
               rewrite Nth1 in H10 ; clear Nth1.
               rewrite H3 in *|-* ; auto.
               intros.
               rewrite MP.ssubst_eapp ; auto.

              (* Case not svalue 0 e1_1 *)
              remember (S.CRaw.svalueb 0 e3).
              destruct b ; symmetry in Heqb0.
              
              (* Case svalue 0 e3 *)
              apply CalculusProperties.svalueb_iff in Heqb0.
              unfold admin_ssubst ; intros ;
              apply Admin_trans with (e2:=
              (bind (ret (phi e3 (map_iter_booker e1_2 bs 0)))
              (fun v1 : T.expr => bind e0 (fun v2 : T.expr => cast_eapp v1 v2)))) ;
              [|apply Admin_bind_phi ; auto] ;
              rewrite MP.ssubst_bind with (f2:=(fun v1 : T.expr => bind e0 (fun v2 : T.expr => cast_eapp v1 v2))).
              destruct H7 ;
              unfold admin_ssubst in H7.
              assert((nth 0 (map_iter_booker e1_2 bs 0) 0 + booker e1_1 0) = 
              (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0)))%nat as Eq1.
              destruct bs ; [exfalso |] ; simpl in *|-* ; omega.
              rewrite Eq1, SValuePhi3 in H7 ; auto ; rewrite <- H3 in H7.
              constructor ; intros ; auto ; constructor.
              
              intros.
              rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr =>
                cast_eapp (ssubst (depth e1_2)
                match depth e1_2 with
                | 0 => ss | 1 => ss
                | S (S n) => if ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))
                then StageSet.add (S n) ss else ss  end (cast_var (hole_var v)) v2 (phi x (0 :: nil))) v0)).
              assert(nth (length t1) (map_iter_booker e1_2 bs 0) 0 = 
                nth (length t1) bs 0 + booker e1_2 (pred (depth e1_2)))%nat as Nth1.
              rewrite H3, DpthLength3 ; simpl.
              specialize (List2Properties.map_iter_nth_indep 
                   (fun b n : nat => (b + booker e1_2 n)%nat)
                   bs (length t1) 0 0 0) ; intros MapIter1.
                 unfold map_iter_booker ; rewrite MapIter1.
                 rewrite plus_0_r ; simpl ; omega.
                 rewrite DpthLength3 in BSLength ; simpl in *|-* ; omega.
              rewrite LengthHMatch in *|-* ; auto ; simpl ; 
              try(rewrite Eq2 ; rewrite DpthLength3 in BSLength ; simpl in *|-* ; omega).
              destruct EqSsubstEq1 with (h:=(nth (length t1) (map_iter_booker e1_2 bs 0) 0 + length t4)%nat) 
                (v:=(phi x (0 :: nil))) ; auto.
              rewrite H3 ; simpl in *|-* ; omega.
              rewrite Nth1, H3, DpthLength3 ; simpl ; omega.
              
              unfold eq_ssubst in H10.
              destruct (depth e1_2) ; try(rewrite H10 ; auto).
              destruct n ; try(rewrite H10 ; auto).
              remember (ltb (nth (length t1) (map_iter_booker e1_2 bs 0) 0 + length t4)
              (nth 0 bs 0 + booker e1_2 0)).
              destruct b ; symmetry in Heqb1.
              assert(ltb (nth (length t1) (map_iter_booker e1_2 bs 0) 0 + length t4)
              (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0)) = true) as True1.
              apply leb_iff ; apply leb_iff in Heqb1 ; omega.
              rewrite True1, H10 ; auto.
              rewrite H10 ; auto.
              destruct (ltb (nth (length t1) (map_iter_booker e1_2 bs 0) 0 + length t4)
              (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))) ; auto.
              rewrite <- StageSetProperties.ub_le_1 ; auto.
              intros ; rewrite MP.ssubst_eapp ; auto.
              

              (* Case not svalue 0 e3 *)
              unfold admin_ssubst ; intros.
              rewrite MP.ssubst_bind with (f2:=(fun v1 : T.expr => bind e0 (fun v2 : T.expr => cast_eapp v1 v2))).
              destruct H7.
              unfold admin_ssubst in H7.
              assert((nth 0 (map_iter_booker e1_2 bs 0) 0 + booker e1_1 0) = 
              (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0)))%nat as Eq1.
              destruct bs ; [exfalso |] ; simpl in *|-* ; omega.
              rewrite Eq1 in H7 ; auto ; rewrite <- H3 in H7.
              constructor ; intros ; auto ; constructor.
              
              intros.
              rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr =>
                cast_eapp (ssubst (depth e1_2)
                match depth e1_2 with
                | 0 => ss | 1 => ss
                | S (S n) => if ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))
                then StageSet.add (S n) ss else ss  end (cast_var (hole_var v)) v2 (phi x (0 :: nil))) v0)).
              assert(nth (length t1) (map_iter_booker e1_2 bs 0) 0 = 
                nth (length t1) bs 0 + booker e1_2 (pred (depth e1_2)))%nat as Nth1.
              rewrite H3, DpthLength3 ; simpl.
              specialize (List2Properties.map_iter_nth_indep 
                   (fun b n : nat => (b + booker e1_2 n)%nat)
                   bs (length t1) 0 0 0) ; intros MapIter1.
                 unfold map_iter_booker ; rewrite MapIter1.
                 rewrite plus_0_r ; simpl ; omega.
                 rewrite DpthLength3 in BSLength ; simpl in *|-* ; omega.
              rewrite LengthHMatch in *|-* ; auto ; simpl ; 
              try(rewrite Eq2 ; rewrite DpthLength3 in BSLength ; simpl in *|-* ; omega).
              destruct EqSsubstEq1 with (h:=(nth (length t1) (map_iter_booker e1_2 bs 0) 0 + length t4)%nat) 
                (v:=(phi x (0 :: nil))) ; auto.
              rewrite H3 ; simpl in *|-* ; omega.
              rewrite Nth1, H3, DpthLength3 ; simpl ; omega.
              unfold eq_ssubst in H10.
              destruct (depth e1_2) ; try(rewrite H10 ; auto).
              destruct n ; try(rewrite H10 ; auto).
              remember (ltb (nth (length t1) (map_iter_booker e1_2 bs 0) 0 + length t4)
              (nth 0 bs 0 + booker e1_2 0)).
              destruct b ; symmetry in Heqb1.
              assert(ltb (nth (length t1) (map_iter_booker e1_2 bs 0) 0 + length t4)
              (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0)) = true) as True1.
              apply leb_iff ; apply leb_iff in Heqb1 ; omega.
              rewrite True1, H10 ; auto.
              rewrite H10 ; auto.
              destruct (ltb (nth (length t1) (map_iter_booker e1_2 bs 0) 0 + length t4)
              (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))) ; auto.
              rewrite <- StageSetProperties.ub_le_1 ; auto.
              intros ; rewrite MP.ssubst_eapp ; auto.

            (* patch *)
            intros ; inversion H8.

            (* Case not svalue *)
            exists x0.
            destruct H4 ; destruct H5 ; destruct H6 ; 
            destruct H7 ; subst ; repeat(split) ; auto.
            rewrite trans_memory_depth_0 with (bs2:=bs) in H4 ; auto.
            rewrite trans_memory_depth_0 with (bs1:=(map_iter_booker e1_2 bs 0)) (bs2:=bs) in H4 ; auto.
            tauto.
            rewrite H6 ; rewrite H7 ; auto.
            omega.
            intros ; rewrite H7 ; auto.
            rewrite <- H3 ; auto.
            unfold trans_expr ; destruct (trans x0).
            simpl.
            specialize (ContextStaticProperties.unshift_spec t5 ((e, v) :: t4)) ; intros Spec1.
            rewrite Spec1 ; clear Spec1.
            specialize (ContextStaticProperties.unshift_spec (Context.merge t5 t7) ((e, v) :: t4 ++ t6)) ; intros Spec2.
            rewrite Spec2 ; clear Spec2.
            specialize (ContextStaticProperties.shift_spec t0) ; intros Spec3.
            rewrite <- Merge3 in Spec3.
            destruct t0 ; simpl.
            simpl in Merge3 ; inversion Merge3.
            rewrite ContextStaticProperties.merge_nil_r.
            rewrite ContextStaticProperties.merge_nil_r.
            rewrite app_nil_r ; auto.
            rewrite Spec3 ; simpl ; auto ; [|omega].
            rewrite ContextStaticProperties.merge_app ; auto.
            rewrite DpthLength4, DpthLength3 in H3.
            specialize (ContextStaticProperties.shift_length (t0 :: t9)) ; intros L1.
            specialize (ContextStaticProperties.shift_length (t :: t1)) ; intros L2.
            rewrite <- Merge3 in L1.
            rewrite <- Merge2 in L2.
            rewrite L1, L2, H3 ; auto.
            
          (* Case depth(e1) > depth(e2) *)
          assert(depth e1_2 < depth e1_1) as D1.
          omega.
          rewrite H2 in *|-*.
          clear H3 H2 m ; assert(H3:=D1).
          rewrite ContextStaticProperties.shift_merge_1 ;
          [| rewrite DpthLength4 in H3 ; rewrite DpthLength3 in H3] ; auto.
          destruct (Context.merge (t::t1) t0).
          simpl in Merge1 ; destruct t0 ; inversion Merge1.
          assert (Context.shift (t::t1) =  Context.shift ((fun x => x) (t::t1))) as Merge2.
          reflexivity.
          destruct (Context.shift (t :: t1)).
          assert (Context.shift t0 =  Context.shift ((fun x => x) t0)) as Merge3.
          reflexivity.
          destruct (Context.shift t0).
          destruct t4 ; [exfalso |] ; auto ; simpl.
          destruct p.
          specialize (svalue_phi e3 (map_iter_booker e1_2 bs 0)) ; 
          intros SValuePhi3 ; unfold trans_expr in SValuePhi3.
          specialize (AdminSsubst2 e3).
          destruct (trans e3).
          destruct IHe1_1.
          exists x.
          destruct H2 ; split ; auto.
          destruct H4 ; [left|right] ; destruct H4.

            (* Case svalue *)
            destruct H5 ; destruct H6.
            repeat(split) ; auto.
            apply AdminSsubst2 ; auto.
            
            remember (S.CRaw.svalueb 0 e1_1).
            destruct b ; symmetry in Heqb.

              (* Case svalue 0 e1_1 *)
              apply CalculusProperties.svalueb_iff in Heqb.
              assert(svalue 0 e3) as SValueE3.
                inversion Heqb ; subst ; 
                try(inversion H1 ; constructor ; fail).
                inversion H1 ; subst ; simpl in *|-*.
                apply CalculusProperties.depth_svalue in H8.
                exfalso ; omega.
              apply CalculusProperties.svalueb_iff in SValueE3.
              rewrite SValueE3.
              unfold admin_ssubst ; intros.
              rewrite MP.ssubst_bind with (f2:=
                fun v2 => cast_eapp (
                ssubst (depth e1_1)
                 match depth e1_1 with
                 | 0 => ss
                 | 1 => ss
                 | S (S n) =>
                 if ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))
                 then StageSet.add (S n) ss
                 else ss
                 end (cast_var (hole_var v))
                 (phi e1_1 (map_iter_booker e1_2 bs 0)) (phi x (0 :: nil)))
               v2) ; auto.
               constructor ; auto.
               simpl in *|-*.
               destruct EqSsubstEq2 with (m:=depth e1_1) (h:=v) (v:=(phi x (0 :: nil))) ; auto.
               unfold eq_ssubst in H10.
               remember (ltb v (nth 0 bs 0 + booker e1_2 0)).
               destruct b ; symmetry in Heqb0.
               assert(ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0)) = true) as True1.
                 apply leb_iff ; apply leb_iff in Heqb0 ; omega.
               rewrite True1, H10 ; auto ; try(omega) ; constructor.
               destruct (depth e1_1) ; try(rewrite H10 ; auto ; try(omega) ; constructor).
               destruct n ; try(rewrite H10 ; auto ; try(omega) ; constructor).
               rewrite H10 ; auto ; try(omega) ; [constructor |].
               destruct (ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))) ; auto.
               rewrite <- StageSetProperties.ub_le_1 ; auto.
               intros.
               constructor ; [|constructor].
               destruct H7.
               specialize (H10 Heqb).
               unfold admin_ssubst in H10.
               assert((nth 0 (map_iter_booker e1_2 bs 0) 0 + booker e1_1 0)%nat
               = (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))%nat) as Nth1.
                 specialize (List2Properties.map_iter_nth_indep 
                   (fun b n : nat => (b + booker e1_2 n)%nat)
                   bs 0 0 0 0) ; intros MapIter1.
                 unfold map_iter_booker ; rewrite MapIter1.
                 simpl ; clear ; omega.
                 destruct (depth e1_1) ; omega.
               rewrite Nth1 in H10 ; clear Nth1 ; auto.
               intros ; rewrite MP.ssubst_eapp ; auto.

              (* Case not svalue 0 e1_1 *)
              remember (S.CRaw.svalueb 0 e3).
              destruct b ; symmetry in Heqb0.
              
              (* Case svalue 0 e3 *)
              apply CalculusProperties.svalueb_iff in Heqb0.
              unfold admin_ssubst ; intros ;
              apply Admin_trans with (e2:=
              (bind (ret (phi e3 (map_iter_booker e1_2 bs 0)))
              (fun v1 : T.expr => bind e0 (fun v2 : T.expr => cast_eapp v1 v2)))) ;
              [|apply Admin_bind_phi ; auto] ;
              rewrite MP.ssubst_bind with (f2:=(fun v1 : T.expr => bind e0 (fun v2 : T.expr => cast_eapp v1 v2))).
              destruct H7 ;
              unfold admin_ssubst in H7.
              assert((nth 0 (map_iter_booker e1_2 bs 0) 0 + booker e1_1 0) = 
              (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0)))%nat as Eq1.
              destruct bs ; [exfalso |] ; simpl in *|-* ; omega.
              rewrite Eq1, SValuePhi3 in H7 ; auto ;
              constructor ; intros ; auto ; constructor.
              
              intros.
              rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr =>
                cast_eapp (ssubst (depth e1_1)
                match depth e1_1 with
                | 0 => ss | 1 => ss
                | S (S n) => if ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))
                then StageSet.add (S n) ss else ss  end (cast_var (hole_var v)) v2 (phi x (0 :: nil))) v0)).
              destruct EqSsubstEq2 with (m:=depth e1_1) (h:=v) (v:=(phi x (0 :: nil))) ; auto.
               unfold eq_ssubst in H10.
               remember (ltb v (nth 0 bs 0 + booker e1_2 0)).
               destruct b ; symmetry in Heqb1.
               assert(ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0)) = true) as True1.
                 apply leb_iff ; apply leb_iff in Heqb1 ; omega.
               rewrite True1, H10 ; auto ; try(omega) ; constructor.
               destruct (depth e1_1) ; try(rewrite H10 ; auto ; try(omega) ; constructor).
               destruct n ; try(rewrite H10 ; auto ; try(omega) ; constructor).
               rewrite H10 ; auto ; try(omega).
               destruct (ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))) ; auto.
               rewrite <- StageSetProperties.ub_le_1 ; auto.
              intros ; rewrite MP.ssubst_eapp ; auto.
              

              (* Case not svalue 0 e3 *)
              unfold admin_ssubst ; intros.
              rewrite MP.ssubst_bind with (f2:=(fun v1 : T.expr => bind e0 (fun v2 : T.expr => cast_eapp v1 v2))).
              destruct H7.
              unfold admin_ssubst in H7.
              assert((nth 0 (map_iter_booker e1_2 bs 0) 0 + booker e1_1 0) = 
              (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0)))%nat as Eq1.
              destruct bs ; [exfalso |] ; simpl in *|-* ; omega.
              rewrite Eq1 in H7 ; auto.
              constructor ; intros ; auto ; constructor.

              intros.
              rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr =>
                cast_eapp (ssubst (depth e1_1)
                match depth e1_1 with
                | 0 => ss | 1 => ss
                | S (S n) => if ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))
                then StageSet.add (S n) ss else ss  end (cast_var (hole_var v)) v2 (phi x (0 :: nil))) v0)).
              destruct EqSsubstEq2 with (m:=depth e1_1) (h:=v) (v:=(phi x (0 :: nil))) ; auto.
               unfold eq_ssubst in H10.
               remember (ltb v (nth 0 bs 0 + booker e1_2 0)).
               destruct b ; symmetry in Heqb1.
               assert(ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0)) = true) as True1.
                 apply leb_iff ; apply leb_iff in Heqb1 ; omega.
               rewrite True1, H10 ; auto ; try(omega) ; constructor.
               destruct (depth e1_1) ; try(rewrite H10 ; auto ; try(omega) ; constructor).
               destruct n ; try(rewrite H10 ; auto ; try(omega) ; constructor).
               rewrite H10 ; auto ; try(omega).
               destruct (ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))) ; auto.
               rewrite <- StageSetProperties.ub_le_1 ; auto.
              intros ; rewrite MP.ssubst_eapp ; auto.

            (* patch *)
            intros ; inversion H8.

            (* Case not svalue *)
            exists x0.
            destruct H4 ; destruct H5 ; destruct H6 ; 
            destruct H7 ; subst ; repeat(split) ; auto.
            rewrite trans_memory_depth_0 with (bs2:=bs) in H4 ; auto.
            rewrite trans_memory_depth_0 with (bs1:=(map_iter_booker e1_2 bs 0)) (bs2:=bs) in H4 ; auto.
            tauto.
            rewrite H6 ; rewrite H7 ; auto.
            omega.
            intros ; rewrite H7 ; auto.
            unfold trans_expr ; destruct (trans x0).
            simpl.
            rewrite merge_unshift_1 ; auto.
            specialize (ContextStaticProperties.shift_length (t :: t1)) ; intros L1.
            rewrite <- Merge2 in L1.
            rewrite L1 ; simpl in *|-*.
            rewrite DpthLength3, DpthLength4 in *|-*.
            generalize D1 ; clear ; intros.
            apply le_S_n in D1 ; auto.

      (* Case EApp e1 e2,  e2 -> e2' *)
      specialize (max_spec (depth e1_2) (depth e1_1)) ; intros MaxRight.
      destruct MaxRight ; destruct H ; rewrite max_comm in H0.
      rewrite H0 in H6.
      specialize (CalculusProperties.depth_sstep_lt 
        M1 e1_2 M2 e0 (depth e1_1) H H6) ;
      intros ; contradiction.
      rewrite H0 in *|-* ; clear IHe1_1.
      specialize (IHe1_2 bs e0 M1 M2 MemSvalue0 MemDepth0 BSLength H6).
      specialize (depth_length e1_1 (map_iter_booker e1_2 bs 0)) ; intros DpthLength3.
      specialize (depth_length e1_2 bs) ; intros DpthLength4.
      unfold trans_expr ; simpl.
      destruct (trans e1_2).
      destruct t.
 
        (* Case EApp e1 e2, n = 0, e2 -> e2' *)
        rewrite DpthLength4 in H ; apply le_n_0_eq in H.
        rewrite trans_depth_0 with (bs1:=map_iter_booker e0 bs 0) (bs2:=map_iter_booker e1_2 bs 0) ; auto.
        destruct (trans e1_1).
        destruct t ; [|exfalso ; simpl in *|-* ; omega] ; simpl.
        simpl in *|-*.
        rewrite DpthLength4 in *|-*.
        assert(S.CRaw.svalueb 0 e1_1 = true) as SValuebTrue.
        apply CalculusProperties.svalueb_iff ; auto.
        rewrite SValuebTrue.
        unfold trans_expr in IHe1_2 ; destruct (trans e0).
        inversion IHe1_2 ; subst.
        apply Rel_step with (e1:=bind e3
        (fun v2 => cast_eapp (phi e1_1 (map_iter_booker e1_2 bs 0)) v2)).
        apply MP.astep_bind_app_svalue ; auto.
        constructor ; auto.
        intros ; rewrite phi_depth_0 with (bs2:=(map_iter_booker e0 bs 0)) ; auto.
        constructor.

        (* Case EApp e1 e2, n > 0, e2 -> e2' *)
        admit.

      (* Case EApp (EAbs), n = 0 *)
      symmetry in H ; apply max_0 in H.
      destruct H.
      clear IHe1_2 IHe1_1.
      specialize (svalue_phi (CRaw.EAbs x e) (map_iter_booker e1_2 bs 0)) ; intros SValuePhi1.
      specialize (depth_length e (map_iter_booker e1_2 bs 0)) ; intros DpthLength1.
      unfold trans_expr in SValuePhi1 ; simpl trans in SValuePhi1 ;
      specialize (trans_ssubst_source e e1_2 bs x StageSet.empty 0) ; intros TSS.
      rewrite trans_depth_0 with (bs2:=(map_iter_booker e1_2 bs 0)) in TSS ; auto.
      destruct (trans e).
      rewrite H in DpthLength1 ; destruct t ;
      [clear DpthLength1 |inversion DpthLength1].
      specialize (depth_length e1_2 bs) ; intros DpthLength2.
      specialize (svalue_phi e1_2 bs H1) ; intros SValuePhi2.
      unfold trans_expr in SValuePhi2 ;
      destruct (trans e1_2).
      rewrite H0 in DpthLength2 ; destruct t ;
      [clear DpthLength2 |inversion DpthLength2].
      simpl.
      apply Rel_step with 
      (e1:=trans_expr (S.ssubst 0 StageSet.empty x e e1_2) bs).
      rewrite SValuePhi2 ; auto.
      apply MP.astep_bind_2 ; auto.
      destruct TSS ; auto.
      unfold trans_expr ; rewrite H2 ; auto.
      apply MP.astep_app_abs ; auto.
      constructor.

      (* Case EApp (EFix), n = 0 *)
      symmetry in H ; apply max_0 in H.
      destruct H.
      clear IHe1_2 IHe1_1.
      specialize (svalue_phi (CRaw.EFix f x e) (map_iter_booker e1_2 bs 0)) ; intros SValuePhi1.
      specialize (depth_length e (map_iter_booker e1_2 bs 0)) ; intros DpthLength1.
      unfold trans_expr in SValuePhi1 ; simpl trans in SValuePhi1 ;
      specialize (trans_ssubst_source e e1_2 bs x StageSet.empty 0) ; intros Ssubst2.
      specialize (trans_ssubst_source (S.ssubst 0 StageSet.empty x e e1_2) 
        (CRaw.EFix f x e) bs f StageSet.empty 0) ; intros Ssubst1.
      simpl in Ssubst1.
      rewrite trans_depth_0 with (e:=e) (bs2:=(map_iter_booker e1_2 bs 0)) in Ssubst1 ; auto.
      rewrite trans_depth_0 with (bs2:=(map_iter_booker e1_2 bs 0)) in Ssubst2 ; auto.
      destruct (trans e).
      rewrite H in DpthLength1 ; destruct t ;
      [clear DpthLength1 |inversion DpthLength1].
      specialize (depth_length e1_2 bs) ; intros DpthLength2.
      specialize (svalue_phi e1_2 bs H1) ; intros SValuePhi2.
      unfold trans_expr in SValuePhi2 ;
      destruct (trans e1_2).
      rewrite H0 in DpthLength2 ; destruct t ;
      [clear DpthLength2 |inversion DpthLength2].
      simpl.
      apply Rel_step with 
      (e1:=trans_expr (CRaw.ssubst 0 StageSet.empty f 
        (CRaw.ssubst 0 StageSet.empty x e e1_2)
        (CRaw.EFix f x e)) bs).
      rewrite SValuePhi2 ; auto.
      apply MP.astep_bind_2 ; auto.
      unfold trans_expr.
      destruct Ssubst2 ; auto.
      rewrite H2 in Ssubst1 ; auto.
      destruct Ssubst1 ; auto.
      constructor.
      assert(CRaw.ssubst = S.ssubst) as Eq1.
      reflexivity.
      rewrite Eq1, H4 ; auto.
      apply MP.astep_app_fix ; auto.
      constructor.

    (* Case ELoc *)
    inversion Step.

    (* Case ERef *)
    specialize (depth_length e1 bs) ; intros DpthLength.
    inversion Step ; subst.
    specialize (IHe1 bs).
    destruct (trans e1).
    destruct t ; intros.

      (* SubCase ERef, n=0, e -> e' *)
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      unfold trans_expr in *|-* ; simpl in *|-*.
      inversion IHe1 ; subst.
      apply Rel_step with (e1:=bind e0 (fun v => cast_eref v)) ; auto.
      apply MP.astep_bind_eref ; assumption.
      destruct (trans e3).
      constructor ; [auto | intros ; constructor].

      (* SubCase ERef, n>0 *)
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      destruct (Context.shift (t :: t0)).
      destruct t1 ; simpl in *|-* ; auto.
      destruct p ; destruct (trans e3) ; intros.
      destruct IHe1 ; exists x.
      destruct H ; split ; [assumption|].
      destruct H0 ; [left | right] ; destruct H0.

        (* Case svalue *)
        destruct H2 ; destruct H3 ; destruct H4 ; subst.
        repeat(split ; auto).
        unfold admin_ssubst ; intros.
        rewrite MP.ssubst_bind with (f2:=fun v0 => cast_eref v0).
        constructor ; auto.
        intros ; constructor.
        intros.
        rewrite MP.ssubst_eref ; auto.
        
        (* patch *)
        intros SV ; inversion SV. 

        (* Case not svalue *)
        exists x0.
        destruct H0 ; destruct H2 ; destruct H3 ; 
        destruct H4 ; subst ; auto.
        repeat(split) ; intros ; auto.
        rewrite H4 ; auto.

      (* SubCase ERef, n=0, svalue 0 e *)
      specialize (svalue_phi e1 bs H1) ; intros SValuePhi.
      unfold trans_expr in SValuePhi.
      destruct (trans e1 bs).
      rewrite <- H in DpthLength ; destruct t ; [|inversion DpthLength].
      unfold trans_expr in *|-* ; clear IHe1 ; subst.
      apply Rel_step with (e1:=ret (cast_eloc (CRaw.Memory.fresh M1))).
      apply MP.astep_bind_2 ; auto.
      rewrite trans_mem_set ; auto.
      rewrite <- trans_mem_fresh with (bs:=bs) ; auto.
      apply MP.astep_eref ; auto.
      simpl ; constructor.

    (* Case EDeref *)
    specialize (depth_length e1 bs) ; intros DpthLength.
    inversion Step ; subst.
    specialize (IHe1 bs).
    destruct (trans e1).
    destruct t ; intros.

      (* SubCase EDeref, n=0, e -> e' *)
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      unfold trans_expr in *|-* ; simpl in *|-*.
      inversion IHe1 ; subst.
      apply Rel_step with (e1:=bind e0 (fun v => cast_ederef v)) ; auto.
      apply MP.astep_bind_ederef ; assumption.
      destruct (trans e3).
      constructor ; [auto | intros ; constructor].

      (* SubCase EDeref, n>0 *)
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      destruct (Context.shift (t :: t0)).
      destruct t1 ; simpl in *|-* ; auto.
      destruct p ; destruct (trans e3) ; intros.
      destruct IHe1 ; exists x.
      destruct H ; split ; [assumption|].
      destruct H0 ; [left | right] ; destruct H0.

        (* Case svalue *)
        destruct H2 ; destruct H3 ; destruct H4 ; subst.
        repeat(split ; auto).
        unfold admin_ssubst ; intros.
        rewrite MP.ssubst_bind with (f2:=fun v0 => cast_ederef v0).
        constructor ; auto.
        intros ; constructor.
        intros.
        rewrite MP.ssubst_ederef ; auto.

        (* patch *)
        intros SV ; inversion SV.

        (* Case not svalue *)
        exists x0.
        destruct H0 ; destruct H2 ; destruct H3 ; 
        destruct H4 ; subst ; auto.
        repeat(split) ; intros ; auto.
        rewrite H4 ; auto.

      (* SubCase EDeref, n=0, svalue 0 e *)
      simpl.
      apply Rel_step with (e1:=trans_expr (CRaw.Memory.get l M2) bs).
      assert(phi (CRaw.ELoc l) bs = (cast_eloc l)) as Phi1.
      reflexivity.
      rewrite <- Phi1.
      apply MP.astep_bind_2 with (v:=CRaw.ELoc l) (bs:=bs) ; try(constructor).
      rewrite svalue_phi.
      rewrite trans_mem_get ; auto.
      apply MP.astep_ederef ; auto.
      rewrite trans_mem_length ; auto.
      apply CalculusProperties.memory_svalue_get ; auto.
      simpl ; constructor.

    (* Case EAssign *)
    admit.

    (* Case EBox *)
    specialize (IHe1 (0::bs)).
    specialize (length_svalue e1 (0::bs) 0) ; intros LthSvalue.
    specialize (context_stack_not_nil e1 (0::bs)) ; intros CSNotNil.
    specialize (depth_length e1 (0::bs)) ; intros DpthLength.
    specialize (context_mem e1 (0::bs)) ; intros CMem1.
    specialize (admin_fill_ssubst e1 bs) ; intros FillSubst.
    specialize (booker_length e1 (0::bs)) ; intros BKLength1.
    inversion Step ; subst ; simpl in *|-*.
    destruct (trans e1).
    specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0).
    destruct t ; simpl in *|-* ; intros.

      (* Case of svalue 1 e1. Impossible *)
      rewrite DpthLength in H1 ; simpl in *|-* ; exfalso.
      apply CalculusProperties.svalue_not_sprogresses in H1 ; auto.
      apply LthSvalue ; auto.

      (* Case of stack > 0 *)
      destruct t0.

        (* Case of length(stack) = 1 *)
        rewrite DpthLength in *|-* ; simpl in *|-*.
        apply le_n_S in BSLength.
        specialize (IHe1 BSLength H1).
        destruct t.

          (* Case stack = [[]] Impossible *)
          contradiction.
   
          (* Case stack = [a :: lst] *)
          destruct p.
          unfold trans_expr ; simpl in *|-*.
          specialize (depth_length e3 (0::bs)) ; intros DpthLength2.
          destruct (trans e3) ; intros.
          destruct IHe1 ; destruct H.
          destruct H0.

            (* Case svalue *)
            destruct H0 ; destruct H2 ; 
            destruct H3 ; destruct H4 ; subst.
            destruct t.

            inversion H3 ; subst.
            rewrite svalue_phi ; auto.
            simpl.
            apply Rel_step with (e1:=
              (M.ssubst 0 StageSet.empty (M.cast_var (hole_var v)) 
                (M.ret (M.cast_ebox e)) (phi x (0 :: nil)))).
            apply MP.astep_bind_2 ; auto.
            apply MP.astep_app_abs ; auto.
            rewrite MP.ssubst_ret, MP.ssubst_ebox ; repeat(constructor).
            apply H4 ; auto.

            inversion H3 ; subst.
            inversion H7 ; subst.
            simpl in *|-*.
            rewrite svalue_phi ; auto.
            apply Rel_step with (e1:=
              M.ssubst 0 StageSet.empty (M.cast_var (hole_var v)) 
                (bind u1 (fun v1 => cast_eapp
                  (cast_eabs (cast_var (hole_var (length t)))
                  (Context.fill t (ret (cast_ebox e))))
                  v1)) (phi x (0 :: nil))).
            apply MP.astep_bind_2 ; auto.
            apply MP.astep_app_abs ; auto.
            assert(1 <= S (S (length bs0))) as Tmp1.
            clear ; omega.
            specialize (FillSubst Tmp1 
              (phi x (0 :: nil)) e2 ((u2,(length t)%nat)::c0) H7 H4).
            apply FillSubst ; auto.

            (* Case not svalue *)
            destruct H0 ; destruct H0 ; 
            destruct H2 ; destruct H3 ; destruct H4 ; subst.
            inversion H0 ; subst.
            apply Rel_step with (e1:=bind e0 (fun v0 =>
               cast_eapp
               (cast_eabs (cast_var (hole_var v))
               (Context.fill t (ret (cast_ebox e2)))) v0)).
            apply MP.astep_bind_app_eabs.
            rewrite trans_memory_depth_0 with (bs2:=0::bs) ; auto.
            rewrite trans_memory_depth_0 with (bs1:=bs) (bs2:=0::bs).
            assumption.
            rewrite <- DpthLength in H1.
            apply CalculusProperties.depth_sstep_eq in H1 ; auto.
            destruct H1 ; assumption.
            simpl ; constructor ;
            [assumption | intros ; constructor].

        (* Case of length(stack) > 1 *)
        rewrite DpthLength in H1, BSLength.
        simpl in H1, DpthLength, BSLength.
        rewrite <- DpthLength in H1.
        apply le_n_S in BSLength.
        rewrite <- DpthLength in BSLength.
        specialize (IHe1 BSLength H1).
        assert(length (t0 :: t1) > 0) as Tmp1.
        simpl ; clear IHe1 LthSvalue ; omega.
        assert(~ In nil (t0 :: t1)) as Tmp2.
        unfold not ; intros ; apply CSNotNil.
        right ; auto.
        specialize (context_shift_not_nil (t0::t1) Tmp1 Tmp2) ; 
        intros CSShiftNotNil ; clear Tmp1 Tmp2.
        assert(Context.shift (t0 :: t1) = Context.shift ((fun x => x) (t0 :: t1))) as Shift1.
        reflexivity.
        destruct (Context.shift (t0 :: t1)).
        destruct CSShiftNotNil.
        destruct t2 ; [exfalso ; auto |].
        destruct p ; destruct (trans e3) ; intros.
        destruct IHe1.
        destruct H2.
        destruct H3 ; subst.

          (* Case svalue *)
          destruct H3 ; subst.
          destruct H3 ; destruct H3 ; subst.
          destruct H4 ; destruct H4.
          destruct t2 ; simpl in *|-*.

          inversion H3 ; subst.
          exists x ; split ; auto ; left.
          repeat(split; auto) ; simpl.
          constructor.
          destruct t1 ; [|destruct (Context.shift (t1 :: t2))] ; 
          inversion Shift1 ; subst.
          rewrite DpthLength in *|-* ; simpl in *|-*.
          apply FillSubst ; simpl ; auto.
          clear ; omega.

          (* patch *)
          intros VL.
          inversion VL ; subst.
          apply LthSvalue in H8.
          exfalso ; generalize H8 ; clear ; intros ; omega.
         
          exists x ; split ; auto ; left.
          repeat(split; auto) ; simpl.
          destruct t1 ; [ | destruct (Context.shift (t1 :: t2))] ; 
          inversion Shift1 ; subst.

          apply FillSubst ; auto.
          generalize BSLength ; clear ; intros ; omega.

          (* patch *)
          intros VL.
          inversion VL ; subst.
          apply LthSvalue in H8.
          exfalso ; generalize H8 ; clear ; intros ; omega.
          
          inversion H3 ; subst.
          destruct t3 ; simpl in H10 ; inversion H10.

          exists x ; split ; auto ; left.
          repeat(split; auto) ; simpl.
          destruct t1 ; [ inversion Shift1 ; subst ;
          simpl in H7 ; inversion H7|] ; subst.
          apply FillSubst ; simpl ; auto.
          generalize BSLength ; clear ; simpl ; intros ; omega.
          destruct (Context.shift (t1 :: t4)) ; inversion Shift1 ; subst.
          simpl in H7 ; inversion H7 ; subst ; auto.
          apply FillSubst ; simpl ; auto.
          generalize BSLength ; simpl in *|-* ; clear ; intros ; omega.

          (* patch *)
          intros VL.
          inversion VL ; subst.
          apply LthSvalue in H9.
          exfalso ; generalize H9 ; clear ; intros ; omega.

          (* Case not svalue *)
          destruct H3 ; destruct H2 ; destruct H3 ; 
          destruct H4 ; destruct H5 ; subst.
          exists x ; split ; auto ; right.
          exists x0.
          repeat(split ; auto).
          rewrite trans_memory_depth_0 with (bs2:=0::bs) ; auto.
          rewrite trans_memory_depth_0 with (bs1:=bs) (bs2:=0::bs) ; auto.
          apply CalculusProperties.depth_sstep_eq in H1 ; auto.
          destruct H1 ; assumption.
          intros ; auto.
          apply H5 ; auto.
          rewrite DpthLength in *|-* ; simpl in *|- * ; 
          generalize H3 ; clear ; intros ; omega.

    (* Case EUnbox *)
    destruct bs ; [inversion BSLength|] ; simpl.
    specialize (depth_length e1 bs) ; intros DpthLength1.
    specialize (length_h e1 bs) ; intros LengthH.
    specialize (length_h_match e1 bs) ; intros LengthHMatch.
    specialize (booker_length e1 bs) ; intros BKLength1.
    specialize (IHe1 bs).
    assert(trans e1 bs = trans e1 ((fun x => x) bs)) as TransE1.
    reflexivity.
    destruct (trans e1 bs).
    inversion Step ; subst.

      (* Case EUnbox -> EUnbox *)
      apply le_S_n in BSLength.
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      specialize (depth_length e3 bs) ; intros DpthLength2.
      specialize (CalculusProperties.depth_sstep_eq M1 e1 M2 e3 MemDepth0 H1) ; 
      intros DpthStep ; simpl.
      destruct t.

        (* Case n = 1 *)
        unfold trans_expr in *|-* ; simpl in *|-*.
        assert(trans e3 bs = trans e3 ((fun x => x) bs)) as TransE3.
        reflexivity.
        destruct (trans e3 bs).
        exists e1.
        rewrite trans_depth_0 with (bs2:=bs) ; auto.
        rewrite <- TransE1.
        split ; auto.
        right.
        exists e3.
        destruct DpthStep.
        rewrite DpthLength1 in H ; apply le_n_0_eq in H.
        rewrite trans_depth_0 with (bs2:=bs) ; auto.
        rewrite <- TransE3.
        rewrite trans_memory_depth_0 with (bs2:=bs) ; auto.
        rewrite trans_memory_depth_0 with (bs1:=n::bs) (bs2:=bs) ; auto.
        repeat(split ; auto).
        intros.
        rewrite DpthLength1 in H2.
        destruct m ; auto.
        destruct m ; auto.
        exfalso ; generalize H2 ; clear ; intros ; omega.
        rewrite <- H in DpthLength2 ; destruct t ; 
        inversion DpthLength2 ; auto.

        (* Case n > 1 *)
        assert(Context.shift (t :: t0) = Context.shift ((fun x => x) (t :: t0))) as Shift1.
        reflexivity.
        destruct (Context.shift (t :: t0)).
        destruct t1 ; simpl in *|-*.
        assumption.
        assert(trans e3 bs = trans e3 ((fun x => x) bs)) as TransE3.
        reflexivity.
        destruct p ; destruct (trans e3 bs).
        destruct IHe1.
        exists x.
        destruct H ; split ; auto.
        destruct H0 ; [left | right] ; destruct H0.

          (* Case svalue *)
          destruct H2 ; destruct H3 ; destruct H4.
          repeat(split ; auto).
          destruct bs.
          rewrite DpthLength1 in BSLength ; inversion BSLength.
          destruct t1.
          destruct t2 ; simpl in *|-* ; inversion H3 ; subst ;
          constructor ; rewrite BKLength1 in H4 ; simpl in H4.
          assert(forall e:T.expr, (e,n) = (e, n + (length (tl (0::nil)))))%nat as Tmp1.
          simpl ; rewrite plus_0_r ; reflexivity.
          simpl tl in Tmp1.
          rewrite Tmp1.
          rewrite Tmp1.
          apply CongrCSubst_cons with (u1:=e) (u2:=e2) (c1:=nil)  
            (c2:=nil) (n:=depth e1) (v:=(phi x (0 :: nil)))
            (b1:=n0) (b2:=n) ; auto.
          unfold admin_ssubst ; intros ; simpl.
          rewrite DpthLength1 ; simpl.
          rewrite DpthLength1 in H4 ; simpl in H4.
          unfold admin_ssubst in H4 ; simpl in H4.
          destruct t0.
          simpl in *|-*.
          apply H4 ; auto.
          rewrite DpthLength1 in H2 ; simpl in H2 ; auto.
          simpl in *|-*.
          destruct t1.
          inversion Shift1.
          destruct (Context.shift (t1 :: t2)).
          inversion Shift1.
          constructor.

          destruct t0.
          inversion Shift1 ; subst.
          destruct (Context.shift (t0 :: t2)) ; inversion Shift1 ; subst.
          assert(forall e:T.expr, (e,n) = (e, n + (length (tl (0::nil)))))%nat as Tmp1.
          simpl ; rewrite plus_0_r ; reflexivity.
          simpl tl in Tmp1.
          rewrite Tmp1.
          rewrite Tmp1.
          apply CongrCSubst_cons with (u1:=e) (u2:=e2) (c1:=nil)  
            (c2:=nil) (n:=depth e1) (v:=(phi x (0 :: nil)))
            (b1:=n0) (b2:=n) ; auto.
          constructor ; assumption.

          destruct t0.
          inversion Shift1 ; subst.
          simpl in *|-* ; inversion H3.
          constructor ; auto.
          assert(forall e:T.expr, (e,n) = (e, n + (length (tl (0::nil)))))%nat as Tmp1.
          simpl ; rewrite plus_0_r ; reflexivity.
          simpl tl in Tmp1.
          rewrite Tmp1.
          rewrite Tmp1.
          apply CongrCSubst_cons with (u1:=e) (u2:=e2) (c1:=nil)  
            (c2:=nil) (n:=depth e1) (v:=(phi x (0 :: nil)))
            (b1:=n0) (b2:=n) ; auto.
          destruct t0 ; [inversion Shift1 |].
          destruct (Context.shift (t0 :: t2)) ; inversion Shift1 ; subst.
          assumption.
          constructor ; auto.
          constructor ; auto.

          assert(Context.unshift t2 (p :: t1) = Context.unshift t2 ((fun x => x) (p :: t1))) as Shift2.
          reflexivity.
          destruct (Context.unshift t2 (p :: t1)).
          destruct t2 ; simpl in Shift2 ; inversion Shift2.
          inversion H3 ; subst.
          constructor ; auto.
          assert(forall e:T.expr, (e,n) = (e, n + (length (tl (0::nil)))))%nat as Tmp1.
          simpl ; rewrite plus_0_r ; reflexivity.
          simpl tl in Tmp1.
          rewrite Tmp1.
          rewrite Tmp1.
          
          apply CongrCSubst_cons with (u1:=e) (u2:=e2) (c1:=nil)  
            (c2:=nil) (n:=depth e1) (v:=(phi x (0 :: nil)))
            (b1:=n0) (b2:=n) ; auto.
          rewrite BKLength1 in H4.
          simpl in *|-*.
          rewrite DpthLength1 in H4. 
          rewrite DpthLength1 ; 
          unfold admin_ssubst in H4 ; unfold admin_ssubst ; intros ;
          simpl in *|-*.
          destruct t0 ; simpl in *|-*.
          apply H4 ; auto.
          assert(t4 = t).
          destruct t3 ; simpl.
          inversion Shift1 ; subst.
          simpl in Shift2 ; inversion Shift2 ; auto.
          destruct (Context.shift (t3 :: t5)).
          inversion Shift1 ; subst.
          simpl in Shift2 ; inversion Shift2 ; auto.
          subst.
          auto.
          constructor ; auto.

          constructor ; auto.
          assert(forall e:T.expr, (e,n) = (e, n + (length (tl (0::nil)))))%nat as Tmp1.
          simpl ; rewrite plus_0_r ; reflexivity.
          simpl tl in Tmp1.
          rewrite Tmp1.
          rewrite Tmp1.
          
          apply CongrCSubst_cons with (u1:=e) (u2:=e2) (c1:=nil)  
            (c2:=nil) (n:=depth e1) (v:=(phi x (0 :: nil)))
            (b1:=n0) (b2:=n) ; auto.
          rewrite BKLength1 in H4.
          simpl in *|-*.
          assert(t4 = t).
          destruct t0 ; simpl.
          inversion Shift1 ; subst.
          simpl in Shift2 ; inversion Shift2 ; auto.
          destruct (Context.shift (t0 :: t3)).
          inversion Shift1 ; subst.
          simpl in Shift2 ; inversion Shift2 ; auto.
          subst.
          assumption.
          constructor.


          unfold admin_ssubst ; intros.
          rewrite DpthLength1.
          rewrite MP.ssubst_eunbox.
          simpl.
          rewrite MP.ssubst_evar.
          case_beq_nat v n.
          rewrite <- beq_nat_refl.
          assert(ltb n (n+1) = true).
          clear ; unfold ltb ;
          apply leb_iff ; omega.
          rewrite H8, andb_true_l.
          rewrite BindingSetProperties.rho_false_mem ; auto.
          constructor.
          rewrite StageSetProperties.remove_mem_1 ; auto.
          apply StageSetProperties.add_mem_3.
          assert(beq_nat (hole_var v) (hole_var n) = false).
          apply beq_nat_false_iff ; unfold hole_var ; omega.
          rewrite H8, andb_false_l.
          constructor.

          (* patch *)
          intros VL ; inversion VL.

          (* Case not svalue *)
          exists x0.
          destruct H0 ; destruct H2 ; destruct H3 ; 
          destruct H4 ; subst ; auto.
          repeat(split ; auto).
          rewrite trans_memory_depth_0 with (bs2:=bs) ; auto.
          destruct DpthStep.
          rewrite trans_memory_depth_0 with (bs1:=n::bs) (bs2:=bs) ; auto.
          intros.
          destruct m ; auto.
          rewrite H4 ; simpl ; auto ; generalize H ; clear ; intros ; omega.

      (* Case EUnbox Box e -> e *)
      rewrite <- H in DpthLength1.
      destruct t ; [| inversion DpthLength1] ; simpl in *|-*.
      specialize (CalculusProperties.depth_svalue e2 0) ; intros.
      destruct H0 ; specialize (H2 H1).
      apply le_S_n, le_n_0_eq in H2.
      rewrite trans_depth_0 with (bs2:=0::bs) ; auto.
      specialize (depth_length e2 (0::bs)) ; intros DpthLength3.
      assert(trans e2 (0::bs) = trans e2 ((fun x => x) (0::bs))) as TransE3.
      reflexivity.
      assert((let (e8, _) := trans e2 (0::bs) in e8) = trans_expr e2 (0::bs)) as TransExpr.
      unfold trans_expr ; reflexivity.
      destruct (trans e2 (0::bs)).
      rewrite <- H2 in DpthLength3 ; destruct t ; [|inversion DpthLength3].
      exists (CRaw.EBox e2).
      unfold trans_expr ; simpl.
      rewrite trans_depth_0 with (bs2:=0::bs) ; auto.
      rewrite <- TransE3.
      inversion TransE1 ; subst.
      split ; auto ; left.
      repeat(split ; auto).
      constructor ; auto.
      constructor.

      unfold admin_ssubst ; intros.
      rewrite MP.ssubst_eunbox.
      rewrite MP.ssubst_evar.
      rewrite <- beq_nat_refl, andb_true_l ; simpl.
      rewrite BindingSetProperties.rho_O_true ; auto.
      constructor.
      apply H1.
      rewrite StageSetProperties.remove_mem_3 ; auto.
      specialize (StageSetProperties.ub_pred ss 1) ; intros.
      simpl in H5 ; rewrite H4 in H5 ; symmetry in H5 ; auto.

      (* patch *)
      intros VL ; inversion VL.

    (* Case ERun *)
    specialize (depth_length e1 bs) ; intros DpthLength.
    inversion Step ; subst.
    specialize (IHe1 bs).
    destruct (trans e1).
    destruct t ; intros.

      (* SubCase ERun, n=0, e -> e' *)
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      unfold trans_expr in *|-* ; simpl in *|-*.
      inversion IHe1 ; subst.
      apply Rel_step with (e1:=bind e0 (fun v => cast_erun v)) ; auto.
      apply MP.astep_bind_erun ; assumption.
      destruct (trans e3).
      constructor ; [auto | intros ; constructor].

      (* SubCase ERun, n>0 *)
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      destruct (Context.shift (t :: t0)).
      destruct t1 ; simpl in *|-* ; auto.
      destruct p ; destruct (trans e3) ; intros.
      destruct IHe1 ; exists x.
      destruct H ; split ; [assumption|].
      destruct H0 ; [left | right] ; destruct H0.

        (* Case svalue *)
        destruct H2 ; destruct H3 ; destruct H4 ; subst.
        repeat(split ; auto).
        unfold admin_ssubst ; intros.
        rewrite MP.ssubst_bind with (f2:=fun v0 => cast_erun v0).
        constructor ; auto.
        intros ; constructor.
        intros.
        rewrite MP.ssubst_erun ; auto.

        (* patch *)
        intros VL ; inversion VL.

        (* Case not svalue *)
        exists x0.
        destruct H0 ; destruct H2 ; destruct H3 ;
        destruct H4 ; subst ; auto.
        repeat(split) ; intros ; auto.
        rewrite H4 ; auto.

      (* SubCase ERun, n=0, svalue 0 e *)
      simpl in *|-*.
      specialize (depth_length e2 (0::bs)) ; intros DpthLength2.
      specialize (length_svalue e2 (0::bs)) ; intros SValueLength.
      specialize (svalue_phi (CRaw.EBox e2) bs) ; intros SValuePhi.
      unfold trans_expr in SValuePhi ; simpl trans_expr in *|-*.
      simpl trans in *|-*.
      destruct (trans e2 (0::bs)).
      rewrite <- H in DpthLength ; destruct t ; simpl.
      clear IHe1 ; subst.
      apply Rel_step with (e1:=trans_expr e2 bs).
      assert(svalue 0 (CRaw.EBox e2)) as SValue0Box.
      constructor ; apply SValueLength ; auto.
      rewrite SValuePhi ; auto.
      apply MP.astep_bind_2 ; auto.
      unfold trans_expr.
      specialize (MP.astep_erun (trans_mem M2 bs) e2 bs) ; intros AStepERun.
      assert(phi (CRaw.EBox e2) bs = 
        let (e0,_) := trans e2 (0::bs) in M.cast_ebox e0).
        reflexivity.
      rewrite trans_depth_0 with (bs2:=bs) in H0 ; auto.
      unfold trans_expr in AStepERun.
      destruct (trans e2 bs).
      rewrite H0.
      apply AStepERun ; auto.
      constructor.
      apply SValueLength in H1.
      exfalso ; generalize H1 ; clear ; simpl ; intros ; omega.

    (* Case ELift *)
    specialize (depth_length e1 bs) ; intros DpthLength.
    inversion Step ; subst.
    specialize (IHe1 bs).
    destruct (trans e1).
    destruct t ; intros.

      (* SubCase ELift, n=0, e -> e' *)
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      unfold trans_expr in *|-* ; simpl in *|-*.
      inversion IHe1 ; subst.
      apply Rel_step with (e1:=bind e0 (fun v => cast_elift v)) ; auto.
      apply MP.astep_bind_elift ; assumption.
      destruct (trans e3).
      constructor ; [auto | intros ; constructor].

      (* SubCase ELift, n>0 *)
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      destruct (Context.shift (t :: t0)).
      destruct t1 ; simpl in *|-* ; auto.
      destruct p ; destruct (trans e3) ; intros.
      destruct IHe1 ; exists x.
      destruct H ; split ; [assumption|].
      destruct H0 ; [left | right] ; destruct H0.

        (* Case svalue *)
        destruct H2 ; destruct H3 ; destruct H4 ; subst.
        repeat(split ; auto).
        unfold admin_ssubst ; intros.
        rewrite MP.ssubst_bind with (f2:=fun v0 => cast_elift v0).
        constructor ; auto.
        intros ; constructor.
        intros.
        rewrite MP.ssubst_elift ; auto.

        (* patch *)
        intros VL ; inversion VL.

        (* Case not svalue *)
        exists x0.
        destruct H0 ; destruct H2 ; destruct H3 ; 
        destruct H4 ; subst ; auto.
        repeat(split) ; intros ; auto.
        rewrite H4 ; auto.

      (* SubCase ELift, n=0, svalue 0 e *)
      specialize (svalue_phi e1 bs H1) ; intros SValuePhi.
      unfold trans_expr in SValuePhi.
      unfold trans_expr.
      simpl.
      rewrite trans_depth_0 with (bs1:=0::bs) (bs2:=bs) ; auto.
      destruct (trans e1 bs).
      rewrite <- H in DpthLength ; destruct t ; [|inversion DpthLength].
      clear IHe1 ; subst.
      apply Rel_step with (e1:=ret (cast_ebox (ret (phi e1 bs)))).
      apply MP.astep_bind_2 ; auto.
      apply MP.astep_elift ; auto.
      simpl ; constructor.
  Qed.

  Theorem sstep_rstep_O:
    forall (e1 e2:S.expr) (M1 M2:S.Memory.t),
    let bs := 0::nil in
    depth e1 = 0 ->
    memory_svalue 0 M1 ->
    memory_depth M1 = 0 ->
    S.sstep 0 (M1, e1) (M2, e2) -> 
    rstep (trans_mem M1 bs, trans_expr e1 bs) 
      (trans_mem M2 bs, trans_expr e2 bs).
  Proof.
    intros.
    specialize (sstep_rstep e1 bs e2 M1 M2 H0) ; intros.
    simpl in H3.
    specialize (depth_length e1 bs) ; intros.
    unfold trans_expr ; destruct (trans e1).
    rewrite H in H4 ; destruct t ; [|inversion H4].
    rewrite H in *|-*.
    apply H3 ; auto.
  Qed.

End TranslationStepProperties.
