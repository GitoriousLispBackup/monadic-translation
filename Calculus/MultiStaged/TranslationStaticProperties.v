Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
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

Module Type ContextStaticProperties (R:Replacement) (S:ReplacementCalculus R)
  (T:StagedCalculus) (M:Monad R S T) (C:Context R S T M).

  Import M.
  Import C.

  Lemma merge_length:
    forall (cs1 cs2:t_stack),
    length (merge cs1 cs2) = max (length cs1) (length cs2).
  Proof.
    induction cs1 ; simpl ; intros.
    reflexivity.
    destruct cs2 ; simpl.
    reflexivity.
    rewrite IHcs1.
    reflexivity.
  Qed.

  Lemma merge_nil:
    forall (cs1 cs2:t_stack),
    nil = merge cs1 cs2 -> (cs1 = nil /\ cs2 = nil).
  Proof.
    intros ; destruct cs1 ; destruct cs2 ; simpl in *|-* ; 
    split ; auto ~ ; try(omega) ;
    inversion H.
  Qed.

  Lemma congr_context_app:
    forall (rel:relation T.expr) (c1 c2 c3 c4:t),
    congr_context rel c1 c3 ->
    congr_context rel c2 c4 ->
    congr_context rel (c1++c2) (c3++c4).
  Proof.
    induction c1 ; simpl ; intros.
    inversion H ; subst.
    simpl ; assumption.
    inversion H ; subst.
    constructor.
    apply IHc1 ; assumption.
    assumption.
  Qed.

  Lemma congr_stack_app:
    forall (rel:relation T.expr) (cs1 cs2 cs3 cs4:t_stack),
    congr_stack rel cs1 cs3 ->
    congr_stack rel cs2 cs4 ->
    congr_stack rel (cs1++cs2) (cs3++cs4).
  Proof.
    induction cs1 ; simpl ; intros.
    inversion H ; subst.
    simpl ; assumption.
    inversion H ; subst.
    constructor.
    apply IHcs1 ; assumption.
    assumption.
  Qed.

  Lemma congr_stack_merge:
    forall (rel:relation T.expr) (cs1 cs2 cs3 cs4:t_stack),
    congr_stack rel cs1 cs3 ->
    congr_stack rel cs2 cs4 ->
    congr_stack rel (merge cs1 cs2) (merge cs3 cs4).
  Proof.
    induction cs1 ; simpl ; intros.
    inversion H ; subst.
    simpl ; assumption.
    inversion H ; subst.

    destruct cs2 ;
    inversion H0 ; subst.
    assumption.
    constructor.
    apply IHcs1 ; assumption.
    apply congr_context_app ; assumption.
  Qed.

  Lemma shift_spec:
    forall (cs:t_stack),
    length cs > 0 ->
    let (c, cs') := shift cs in
    cs = cs'++ (c::nil).
  Proof.
    induction cs ; intros ; simpl in *|-*.
    exfalso ; omega.
    destruct cs.
    simpl in *|-* ; reflexivity.
    destruct (shift (t0 :: cs)).
    simpl.
    rewrite IHcs ; simpl ; auto ~.
    omega.
  Qed.

  Lemma shift_spec_2:
    forall (cs:t_stack),
    let (c, _) := shift cs in
    c = nth (pred (length cs)) cs nil.
  Proof.
    induction cs ; intros ; simpl in *|-*.
    reflexivity.
    destruct (shift cs).
    rewrite IHcs.
    destruct cs ; reflexivity.
  Qed.
  
  Lemma unshift_spec:
    forall (cs:t_stack) (c:t),
    unshift cs c = cs ++ (c::nil).
  Proof.
    induction cs ; intros ; simpl in *|-* ; auto ~.
    rewrite IHcs ; auto ~.
  Qed.

  Lemma shift_length:
    forall (cs:t_stack),
    let (_, cs') := shift cs in
    length cs' = pred (length cs).
  Proof.
    induction cs ; simpl ; intros ; auto ~.
    destruct (shift cs).
    destruct cs ; auto ~.
    simpl in IHcs ; simpl ; auto ~.
  Qed.

  Lemma context_hole_set_app:
    forall (c1 c2:t),
    context_hole_set (c1 ++ c2) =
    VarSet.union (context_hole_set c1)
    (context_hole_set c2).
  Proof.
    induction c1 ; simpl ; intros.
    rewrite VarSetProperties.empty_union_1.
    reflexivity.
    destruct a ; simpl in *|-*.
    rewrite IHc1.
    symmetry ; apply VarSetProperties.union_add.
  Qed.

  Lemma merge_nth:
    forall (cs1 cs2:t_stack) (n:nat),
    nth n (merge cs1 cs2) nil = (nth n cs1 nil ++ nth n cs2 nil).
  Proof.
    induction cs1 ; simpl ; intros.
    destruct n ; reflexivity.
    destruct cs2.
    destruct n ; rewrite app_nil_r ; reflexivity.
    simpl.
    destruct n.
    reflexivity.
    rewrite IHcs1.
    reflexivity.
  Qed.

  Lemma merge_nil_r:
    forall (cs:t_stack),
    merge cs nil = cs.
  Proof.
    induction cs ; auto ~.
  Qed.

  Lemma merge_nil_l:
    forall (cs:t_stack),
    merge nil cs = cs.
  Proof.
    induction cs ; auto ~.
  Qed.

  Lemma merge_app:
    forall (cs1 cs2 cs3 cs4:t_stack),
    length cs1 = length cs2 -> 
    merge (cs1++cs3) (cs2++cs4) = (merge cs1 cs2) ++ (merge cs3 cs4).
  Proof.
    induction cs1 ; simpl ; intros.
    destruct cs2 ; [|inversion H] ; auto ~.
    destruct cs2 ; [inversion H|].
    simpl in H ; inversion H ; subst.
    rewrite <- app_comm_cons.
    rewrite IHcs1 ; auto ~.
  Qed.

  Lemma shift_merge_1:
    forall (cs1 cs2:t_stack),
    length cs2 < length cs1 ->
    shift (merge cs1 cs2) = let (c1, cs1) := shift cs1 in (c1, merge cs1 cs2).
  Proof.
    induction cs1 ; simpl ; intros.
    destruct cs2 ; auto ~ ; simpl in *|-* ; exfalso ; omega.
    destruct cs2 ; auto ~ ; simpl in *|-*.
    destruct (shift cs1).
    destruct cs1 ; auto ~.

    rewrite IHcs1 ; auto ~.
    destruct (shift cs1).
    destruct cs1.
    exfalso ; simpl in *|-* ; omega.
    simpl.
    destruct cs2 ; auto ~.
    omega.
  Qed.

  Lemma shift_merge_2:
    forall (cs1 cs2:t_stack),
    length cs2 < length cs1 ->
    shift (merge cs2 cs1) = let (c1, cs1) := shift cs1 in (c1, merge cs2 cs1).
  Proof.
    induction cs1 ; simpl ; intros.
    destruct cs2 ; auto ~ ; simpl in *|-* ; exfalso ; omega.
    destruct cs2 ; auto ~ ; simpl in *|-*.
    destruct (shift cs1).
    destruct cs1 ; auto ~.

    rewrite IHcs1 ; auto ~.
    destruct (shift cs1).
    destruct cs1.
    exfalso ; simpl in *|-* ; omega.
    simpl.
    destruct cs2 ; auto ~.
    omega.
  Qed.

  Lemma shift_merge_3:
    forall (cs1 cs2:t_stack),
    length cs2 = length cs1 ->
    shift (merge cs1 cs2) = 
      let (c1, cs1) := shift cs1 in
      let (c2, cs2) := shift cs2 in
      (c1++c2, merge cs1 cs2).
  Proof.
    induction cs1 ; simpl ; intros.
    destruct cs2 ; auto ~ ; simpl in *|-* ; exfalso ; omega.
    destruct cs2 ; inversion H ; subst ; auto ~ ; simpl in *|-*.
    rewrite IHcs1 ; auto ~.
    destruct (shift cs1).
    destruct (shift cs2).
    destruct cs1 ; destruct cs2 ; auto ~.
    inversion H1 ; subst.
    inversion H1 ; subst.
  Qed.

  Lemma merge_unshift_1:
    forall (cs1 cs2:t_stack) (c:t),
    length cs2 <= length cs1 ->
    unshift (merge cs1 cs2) c = 
    merge (unshift cs1 c) cs2.
  Proof.
    induction cs1 ; intros.
    destruct cs2 ; [|exfalso ; simpl in *|-* ; omega].
    simpl ; auto ~.
    destruct cs2.
    simpl ; auto ~.
    simpl.
    rewrite IHcs1 ; auto ~.
    simpl in *|-* ; omega.
  Qed.

  Lemma merge_unshift_2:
    forall (cs1 cs2:t_stack) (c:t),
    length cs1 <= length cs2 ->
    unshift (merge cs1 cs2) c = 
    merge cs1 (unshift cs2 c).
  Proof.
    intros cs1 cs2 ; generalize dependent cs1.
    induction cs2 ; intros.
    destruct cs1 ; [|exfalso ; simpl in *|-* ; omega].
    simpl ; auto ~.
    destruct cs1.
    simpl ; auto ~.
    simpl.
    rewrite IHcs2 ; auto ~.
    simpl in *|-* ; omega.
  Qed.

  Inductive congr_context_ssubst 
    (P:nat -> S.CRaw.var -> nat -> T.expr -> nat -> T.expr -> T.expr -> Prop) 
    (n:nat) (h:S.CRaw.var)
    (m:nat) (v:T.expr) (b1 b2:nat) : t -> t -> Prop :=
  | CongrCSubst_nil : congr_context_ssubst P n h m v b1 b2 nil nil
  | CongrCSubst_cons : forall (u1 u2:T.expr) (c1 c2:t),
      P n h m v b1 u1 u2 ->
      congr_context_ssubst P n h m v b1 b2 c1 c2 ->
      congr_context_ssubst P n h m v b1 b2
        (cons (u1,(b2+(length c1))%nat) c1) 
        (cons (u2,(b2+(length c1))%nat) c2).

  Inductive congr_stack_ssubst 
    (P:nat -> S.CRaw.var -> nat -> T.expr -> nat -> T.expr -> T.expr -> Prop) 
    (n:nat) (h:S.CRaw.var) (v:T.expr) : 
    list nat -> nat -> t_stack -> t_stack -> Prop :=
  | CongrSSubst_nil : forall (bs:list nat) (b:nat), congr_stack_ssubst P n h v bs b nil nil
  | CongrSSubst_cons_nil: forall (c1 c2:t) (bs:list nat) (b1 b2:nat),
      congr_context_ssubst P n h 0 v b1 b2 c1 c2 ->
      congr_stack_ssubst P n h v (b1::bs) b2 (c1::nil) (c2::nil)
  | CongrSSubst_cons : forall (bs:list nat) (b1 b2:nat) (c1 c2 c1' c2':t) (cs1 cs2:t_stack),
      congr_context_ssubst P n h (length c1') v b1 b2 c1 c2 ->
      congr_stack_ssubst P (pred n) h v bs b1 (c1'::cs1) (c2'::cs2) ->
      congr_stack_ssubst P n h v (b1::bs) b2 (c1::c1'::cs1) (c2::c2'::cs2).

  Lemma congr_context_ssubst_length:
    forall (P:nat -> S.CRaw.var -> nat -> T.expr -> nat -> T.expr -> T.expr -> Prop)
    (c1 c2:t) (n m b1 b2:nat) (h:S.var) (v:T.expr),
    congr_context_ssubst P n h m v b1 b2 c1 c2 ->
    length c1 = length c2.
  Proof.
    induction c1 ; simpl ; intros.
    inversion H ; subst ; auto ~.
    inversion H ; subst ; simpl.
    specialize (IHc1 c3 n m b1 b2 h v H4).
    auto ~.
  Qed.

  Lemma congr_stack_ssubst_length:
    forall (P:nat -> S.CRaw.var -> nat -> T.expr -> nat -> T.expr -> T.expr -> Prop) 
    (cs1 cs2:t_stack) (n:nat) (h:S.CRaw.var) (v:T.expr) (bs:list nat) (b:nat),
    congr_stack_ssubst P n h v bs b cs1 cs2 ->
    length cs1 = length cs2.
  Proof.
    induction cs1 ; simpl ; intros.
    inversion H ; subst ; auto ~.
    inversion H ; subst ; simpl ; auto ~.
    specialize (IHcs1 (c2'::cs3) (pred n) h v bs0 b1 H6).
    simpl in IHcs1 ; rewrite IHcs1 ; auto ~.
  Qed.

  Lemma congr_ssubst_context_app:
    forall (P:nat -> S.CRaw.var -> nat -> T.expr -> nat -> T.expr -> T.expr -> Prop)
    (c1 c2 c3 c4:t) (n m b1 b2:nat) (h:S.var) (v:T.expr),
    congr_context_ssubst P n h m v b1 (b2 + length c2) c1 c3 ->
    congr_context_ssubst P n h m v b1 b2 c2 c4 ->
    congr_context_ssubst P n h m v b1 b2 (c1 ++ c2) (c3 ++ c4).
  Proof.
    induction c1 ; simpl ; intros ;
    inversion H ; subst ; auto ~.
    assert((b2 + length c2 + length c1) = b2 + (length (c1++c2)))%nat as Eq1.
    rewrite app_length ; simpl ; omega.
    rewrite Eq1 ; constructor ; auto ~.
  Qed.

End ContextStaticProperties.

Module ContextStaticPropertiesImpl (R:Replacement) (S:ReplacementCalculus R)
  (T:StagedCalculus) (M:Monad R S T) (C:Context R S T M).
  Include ContextStaticProperties R S T M C.
End ContextStaticPropertiesImpl.

Module Type TranslationStaticProperties (R:Replacement) (S:ReplacementCalculus R)
    (T:StagedCalculus) (M:Monad R S T) (Tr:Translation R S T M).

  Module CalculusProperties := CalculusProperties R S.
  Module ContextStaticProperties := ContextStaticPropertiesImpl R S T M Tr.Context.
  Import Tr.
  Import S.
  Import M.

  Tactic Notation "try_specialize_1" ident(IHe) ident(bs) 
    ident(dg) ident(dgs) ident(v) ident(v0) tactic(t) :=
    try(specialize (IHe bs (dg_eabs dg v) dgs) ; t) ;
    try(specialize (IHe bs (dg_efix dg v v0) dgs) ; t) ;
    try(specialize (IHe bs (dg_eref dg) dgs) ; t) ;
    try(specialize (IHe bs (dg_ederef dg) dgs) ; t) ;
    try(specialize (IHe bs (dg_erun dg) dgs) ; t) ;
    try(specialize (IHe bs (dg_elift dg) dgs) ; t).

  Tactic Notation "try_specialize_2" ident(IHe1) constr(bs1) 
     ident(IHe2) constr(bs2) ident(dg) ident(dgs) tactic(t) :=
     try(specialize (IHe1 bs1 (dg_eapp_l dg) dgs) ;
     specialize (IHe2 bs2 (dg_eapp_r dg) dgs) ; t) ;
     try(specialize (IHe1 bs1 (dg_eassign_l dg) dgs) ;
     specialize (IHe2 bs2 (dg_eassign_r dg) dgs) ; t).

  Lemma depth_length:
    forall (e:expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    let (_, cs) := trans e bs dg dgs in
    depth e = length cs.
  Proof.
    induction e ; simpl ; intros ;

    (* EConst, EVar, ELoc *)
    try(auto ~ ; fail) ;

    (* EAbs, EFix, ERef, EDeref, ERun, ELift *)
    try(try_specialize_1 IHe bs dg dgs v v0 (destruct (trans e) ; auto ~ ; fail)) ;

    (* EApp, EAssign *)
    try(try_specialize_2 IHe1 (map_iter_booker e2 bs 0) IHe2 bs dg dgs
    (destruct (trans e1) ; 
    destruct (trans e2) ;
    simpl ; rewrite ContextStaticProperties.merge_length ; auto ~ ; fail)).

    (* EBox *)
    destruct (depth e).
    specialize (IHe (0::bs) (dg_ebox dg) (dg::dgs)).
    destruct (trans e).
    destruct t ; simpl in *|-*.
    reflexivity.
    inversion IHe.

    specialize (IHe (0::bs) (dg_ebox dg) (dg::dgs)).
    destruct (trans e).
    destruct t ; simpl in *|-*.
    inversion IHe.
    inversion IHe.
    reflexivity.

    (* EUnbox *)
    destruct (List2.hd_cons bs 0).
    destruct (List2.hd_cons dgs dg_empty).
    specialize (IHe l d l0).
    destruct (trans e).
    simpl ; auto ~.
  Qed.

  Lemma length_svalue:
    forall (e:expr) (bs:list nat) (n:nat) (dg:dg_t) (dgs:list dg_t),
    let (_, cs) := trans e bs dg dgs in
    length cs < (S n) <-> svalue (S n) e.
  Proof.
    intros.
    specialize (depth_length e) ; intros.
    specialize (H bs dg dgs).
    destruct (trans e).
    rewrite <- H.
    apply CalculusProperties.depth_svalue.
  Qed.

  Lemma length_sstep:
    forall (e1 e2:expr) (M1 M2:Memory.t) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    sstep (depth e1) (M1,e1) (M2,e2) ->
    memory_depth M1 = 0 ->
    let (_, cs2) := trans e2 bs dg dgs in
    length cs2 <= depth e1.
  Proof.
    intros.
    specialize (CalculusProperties.depth_sstep_eq M1 e1 M2 e2 H0 H) ; intros.
    destruct H1.
    specialize (depth_length e2 bs) ; intros.
    specialize (H3 dg dgs).
    destruct (trans e2).
    rewrite H3 in *|-*.
    assumption.
  Qed.

  Lemma svalue_phi:
    forall (e:expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    svalue 0 e -> trans_expr e bs dg dgs = M.ret dg (phi e bs dg dgs).
  Proof.
    intros ; inversion H ; subst ; simpl ;
    try(reflexivity) ;
    try(unfold trans_expr ; simpl ; 
    destruct (trans e0) ; reflexivity).

    unfold trans_expr.
    simpl.
    inversion H ; subst.
    specialize (length_svalue e0 (0::bs) 0) ; intros.
    specialize (H1 (dg_ebox dg) (dg::dgs)).
    destruct (trans e0).
    apply H1 in H3.
    destruct t ; simpl in *|-*.
    reflexivity.
    exfalso ; clear H1 H ; omega.
  Qed.

  Lemma context_merge_not_nil:
    forall (t1 t2:Context.t_stack),
    In nil (Context.merge t1 t2) -> In nil t1 \/ In nil t2.
  Proof.
    induction t1 ; intros.
    tauto.
    destruct t2 ; simpl in *|-*.
    tauto.
    destruct H.
    apply app_eq_nil in H.
    tauto.
    apply IHt1 in H.
    tauto.
  Qed.

  Lemma context_stack_not_nil:
    forall (e:expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    let (_, cs) := trans e bs dg dgs in
    ~ In nil cs.
  Proof.
    induction e ; intros ; simpl ; 

    (* EConst, EVar, ELoc *)
    auto ~ ;

    (* EAbs, EFix, ERef, EDeref, ERun, ELift *)
    try(try_specialize_1 IHe bs dg dgs v v0 (destruct (trans e) ; auto ~ ; fail)) ;

    (* EApp, EAssign *)
    try(try_specialize_2 IHe1 (map_iter_booker e2 bs 0) IHe2 bs dg dgs
    destruct (trans e1) ; destruct (trans e2) ; unfold not ; intros ;
    apply context_merge_not_nil in H ; tauto ; fail).

    (* EBox *)
    specialize (IHe (0::bs) (dg_ebox dg) (dg::dgs)).
    destruct (trans e).
    destruct t ; simpl.
    tauto.
    unfold not ; intros ; apply IHe.
    simpl ; auto ~.
    
    (* EUnbox *)
    destruct (List2.hd_cons bs 0).
    destruct (List2.hd_cons dgs dg_empty).
    specialize (IHe l d l0).
    destruct (trans e).
    unfold not ; intros ; apply IHe.
    simpl in *|-*.
    destruct H.
    inversion H.
    assumption.
  Qed.

  Lemma context_shift_not_nil:
    forall (cs:Context.t_stack),
    length cs > 0 ->
    ~ In nil cs ->
    let (c, cs) := Context.shift cs in
    c <> nil /\ ~ In nil cs.
  Proof.
    induction cs ; intros ; simpl in *|-*.
    exfalso ; omega.

    destruct cs ;
    apply not_or_and in H0 ; destruct H0 ; auto ~.
    destruct (Context.shift (t :: cs)).
    assert(length (t :: cs) > 0).
    simpl ; omega.
    specialize (IHcs H2 H1).
    destruct IHcs.
    clear H ; split.
    assumption.
    simpl ; apply and_not_or ; auto ~.
  Qed.

  Lemma admin_context_expr:
    forall (k1 k2:Context.t) (e1 e2:T.expr) (dg:dg_t),
    admin_context k1 k2 -> admin e1 e2 ->
    admin (Context.fill dg k1 e1) (Context.fill dg k2 e2).
  Proof.
    unfold admin_context ;
    induction k1 ; intros.
    inversion H ; subst.
    simpl in *|-* ; assumption.
    destruct a ; inversion H ; subst.
    simpl ; apply Admin_bind.
    inversion H ; subst.
    assumption.
    
    intros.
    apply Admin_app.
    apply Admin_abs.

    apply IHk1 ; assumption.
    apply Admin_refl.
  Qed.

  Lemma admin_context_app:
    forall (k1 k2 k3 k4:Context.t),
    admin_context k1 k2 -> admin_context k3 k4 ->
    admin_context (k1 ++ k3) (k2 ++ k4).
  Proof.
    intros.
    apply ContextStaticProperties.congr_context_app ; assumption.
  Qed.

  Lemma admin_context_merge:
    forall (cs1 cs2 cs3 cs4:Context.t_stack),
    admin_stack cs1 cs2 ->
    admin_stack cs3 cs4 ->
    admin_stack (Context.merge cs1 cs3) (Context.merge cs2 cs4).
  Proof.
    intros.
    apply ContextStaticProperties.congr_stack_merge ; assumption.
  Qed.
  
  Lemma trans_depth:
    forall (e:expr) (bs bs1 bs2:list nat),
    depth e <= length bs -> 
      trans e (bs++bs1) = trans e (bs++bs2) /\ 
      phi e (bs++bs1) = phi e (bs++bs2).
  Proof.
    assert(0 <= 0) as Ole.
    auto ~.
    induction e ; intros ; simpl in *|-* ; split ;

    try(reflexivity) ;
    try(specialize (IHe bs bs1 bs2 H) ; destruct IHe ;
    rewrite H0 ; reflexivity) ;
    try(specialize (IHe bs bs1 bs2 H) ; rewrite IHe ; reflexivity) ;

    (* EApp, EAssign *)
    try(destruct bs ; simpl in *|-* ; [
    apply le_n_0_eq in H ; symmetry in H ; apply max_0 in H ;
    destruct H ; rewrite H, H0 in *|-* ;
    specialize (IHe1 nil (map_iter_booker e2 bs1 0) 
      (map_iter_booker e2 bs2 0) Ole) ;
    specialize (IHe2 nil bs1 bs2 Ole) |
    apply Nat.max_lub_iff in H ; destruct H ;
    specialize (IHe1 (map_iter_booker e2 (n::bs) 0) 
    (map_iter_booker e2 bs1 (0+(length (n::bs))))
    (map_iter_booker e2 bs2 (0+(length (n::bs))))) ;
    specialize (IHe2 (n::bs) bs1 bs2 H0) ;
    unfold map_iter_booker in *|-* ;
    rewrite List2Properties.length_map_iter in IHe1 ;
    rewrite <- List2Properties.map_iter_app in IHe1 ;
    rewrite <- List2Properties.map_iter_app in IHe1 ] ;
    destruct (S.CRaw.svalueb) ;
    simpl in *|-* ; 
    destruct IHe1, IHe2 ; auto ~ ;
    [rewrite H1, H2, H3| rewrite H1, H3 | 
    rewrite H1, H2, H3| rewrite H1, H3] ; auto ~ ; fail).

    (* EBox *)
    assert(depth e <= S (length bs)).
    omega.
    specialize (IHe (0::bs) bs1 bs2 H0).
    repeat(rewrite app_comm_cons).
    destruct IHe ; rewrite H1 ; reflexivity.
    assert(depth e <= S (length bs)).
    omega.
    specialize (IHe (0::bs) bs1 bs2 H0).
    repeat(rewrite app_comm_cons).
    destruct IHe ; rewrite H1 ; reflexivity.
    
    (* EUnbox *)
    destruct bs ; simpl in *|-*.
    exfalso ; omega.
    apply le_S_n in H.
    specialize (IHe bs bs1 bs2 H).
    destruct IHe ; rewrite H0 ; reflexivity.
  Qed.

  Lemma trans_depth_0:
    forall (e:expr) (bs1 bs2:list nat),
    depth e = 0 -> trans e bs1 = trans e bs2.
  Proof.
    intros.
    rewrite <- app_nil_l with (l:=bs1).
    rewrite <- app_nil_l with (l:=bs2).
    apply trans_depth.
    simpl ; omega.
  Qed.

  Lemma phi_depth_0:
    forall (v:expr) (bs1 bs2:list nat),
    depth v = 0 -> phi v bs1 = phi v bs2.
  Proof.
    destruct v ; simpl ; intros ; auto ~.
    rewrite trans_depth_0 with (bs2:=bs2) ; auto ~.
    rewrite trans_depth_0 with (bs2:=bs2) ; auto ~.
    assert(depth v <= 1).
    omega.
    specialize (trans_depth v (0::nil) bs1 bs2 H0) ; intros.
    simpl in *|-*.
    destruct H1 ; rewrite H1 ; auto ~.
  Qed.

  Lemma trans_depth_2:
    forall (e:expr) (bs bs1 bs2:list nat) (dg:dg_t) (dgs dgs1 dgs2:list dg_t),
    depth e <= length bs -> 
    depth e <= length dgs ->
      trans e (bs++bs1) dg (dgs++dgs1) = trans e (bs++bs2) dg (dgs++dgs2) /\ 
      phi e (bs++bs1) dg (dgs++dgs1) = phi e (bs++bs2) dg (dgs++dgs2).
  Proof.
    assert(0 <= 0) as Ole.
    auto ~.
    induction e ; intros ; simpl in *|-* ; split ;

    try(reflexivity) ;
    
    (* EAbs *)
    try(specialize (IHe bs bs1 bs2 (dg_eabs dg v) dgs dgs1 dgs2 H H0) ;
    destruct IHe ; rewrite H1 ; reflexivity ; fail) ;

    (* EFix *)
    try(specialize (IHe bs bs1 bs2 (dg_efix dg v v0) dgs dgs1 dgs2 H H0) ;
    destruct IHe ; rewrite H1 ; reflexivity ; fail).

    (* EApp *)
    destruct bs ; simpl in *|-*.

    apply le_n_0_eq in H ; symmetry in H ; apply max_0 in H ;
    destruct H ; rewrite H, H1 in *|-* ;
    specialize (IHe1 nil (map_iter_booker e2 bs1 0) 
      (map_iter_booker e2 bs2 0) (dg_eapp_l dg) dgs dgs1 dgs2 Ole) ;
    specialize (IHe2 nil bs1 bs2 (dg_eapp_r dg) dgs dgs1 dgs2 Ole) ;
    destruct (S.CRaw.svalueb) ;
    simpl in *|-* ; destruct IHe1, IHe2 ; auto ~ ;
    [rewrite H2, H3, H4 | rewrite H2, H4] ; auto ~.

    apply Nat.max_lub_iff in H ; destruct H ;
    apply Nat.max_lub_iff in H0 ; destruct H0 ;
    specialize (IHe1 (map_iter_booker e2 (n::bs) 0) 
    (map_iter_booker e2 bs1 (0+(length (n::bs))))
    (map_iter_booker e2 bs2 (0+(length (n::bs)))) (dg_eapp_l dg) dgs dgs1 dgs2) ;
    specialize (IHe2 (n::bs) bs1 bs2 (dg_eapp_r dg) dgs dgs1 dgs2 H1) ;
    unfold map_iter_booker in *|-* ;
    rewrite List2Properties.length_map_iter in IHe1 ;
    rewrite <- List2Properties.map_iter_app in IHe1 ;
    rewrite <- List2Properties.map_iter_app in IHe1 ;
    destruct (S.CRaw.svalueb) ;
    simpl in *|-* ; 
    destruct IHe1, IHe2 ; auto ~ ;
    [rewrite H3, H4, H5| rewrite H3, H5] ; auto ~ ; fail.

    (* ERef *)
    try(specialize (IHe bs bs1 bs2 (dg_eref dg) dgs dgs1 dgs2 H H0) ;
    destruct IHe ; rewrite H1 ; reflexivity ; fail).

    (* EDeref *)
    try(specialize (IHe bs bs1 bs2 (dg_ederef dg) dgs dgs1 dgs2 H H0) ;
    destruct IHe ; rewrite H1 ; reflexivity ; fail).

    (* EAssign *)
    destruct bs ; simpl in *|-*.

    apply le_n_0_eq in H ; symmetry in H ; apply max_0 in H ;
    destruct H ; rewrite H, H1 in *|-* ;
    specialize (IHe1 nil (map_iter_booker e2 bs1 0) 
      (map_iter_booker e2 bs2 0) (dg_eassign_l dg) dgs dgs1 dgs2 Ole) ;
    specialize (IHe2 nil bs1 bs2 (dg_eassign_r dg) dgs dgs1 dgs2 Ole) ;
    destruct (S.CRaw.svalueb) ;
    simpl in *|-* ; destruct IHe1, IHe2 ; auto ~ ;
    [rewrite H2, H3, H4 | rewrite H2, H4] ; auto ~.

    apply Nat.max_lub_iff in H ; destruct H ;
    apply Nat.max_lub_iff in H0 ; destruct H0 ;
    specialize (IHe1 (map_iter_booker e2 (n::bs) 0) 
    (map_iter_booker e2 bs1 (0+(length (n::bs))))
    (map_iter_booker e2 bs2 (0+(length (n::bs)))) (dg_eassign_l dg) dgs dgs1 dgs2) ;
    specialize (IHe2 (n::bs) bs1 bs2 (dg_eassign_r dg) dgs dgs1 dgs2 H1) ;
    unfold map_iter_booker in *|-* ;
    rewrite List2Properties.length_map_iter in IHe1 ;
    rewrite <- List2Properties.map_iter_app in IHe1 ;
    rewrite <- List2Properties.map_iter_app in IHe1 ;
    destruct (S.CRaw.svalueb) ;
    simpl in *|-* ; 
    destruct IHe1, IHe2 ; auto ~ ;
    [rewrite H3, H4, H5| rewrite H3, H5] ; auto ~ ; fail.

    (* EBox *)
    assert(depth e <= S (length bs)).
    omega.
    specialize (IHe (0::bs) bs1 bs2 (dg_ebox dg) (dg::dgs) dgs1 dgs2 H1).
    repeat(rewrite app_comm_cons).
    destruct IHe.
    simpl in *|-*.
    destruct (depth e) ; simpl ; try(omega).
    rewrite H2 ; reflexivity.
    assert(depth e <= S (length bs)).
    omega.
    specialize (IHe (0::bs) bs1 bs2 (dg_ebox dg) (dg::dgs) dgs1 dgs2 H1).
    repeat(rewrite app_comm_cons).
    destruct IHe.
    destruct (depth e) ; simpl ; try(omega).
    rewrite H2 ; reflexivity.
    
    (* EUnbox *)
    destruct bs ; simpl in *|-*.
    exfalso ; omega.
    destruct dgs ; simpl in *|-*.
    exfalso ; omega.
    apply le_S_n in H ; apply le_S_n in H0.
    specialize (IHe bs bs1 bs2 d dgs dgs1 dgs2 H H0).
    destruct IHe ; rewrite H1 ; reflexivity.

    (* ERun *)
    try(specialize (IHe bs bs1 bs2 (dg_erun dg) dgs dgs1 dgs2 H H0) ;
    destruct IHe ; rewrite H1 ; reflexivity ; fail).

    (* ELift *)
    try(specialize (IHe bs bs1 bs2 (dg_elift dg) dgs dgs1 dgs2 H H0) ;
    destruct IHe ; rewrite H1 ; reflexivity ; fail).
  Qed.

  Lemma trans_depth_3:
    forall (e:expr) (n:nat) (bs bs1 bs2:list nat) (dg:dg_t) (dgs dgs1 dgs2:list dg_t),
    depth e <= length bs -> 
    n <= length dgs ->
    svalue (S n) e ->
      trans e (bs++bs1) dg (dgs++dgs1) = trans e (bs++bs2) dg (dgs++dgs2) /\ 
      phi e (bs++bs1) dg (dgs++dgs1) = phi e (bs++bs2) dg (dgs++dgs2).
  Proof.
    assert(0 <= 0) as Ole.
    auto ~.
    induction e ; intros n bs bs1 bs2 dg dgs dgs1 dgs2 ;
    intros H H0 SValue ; simpl in *|-* ; split ;

    try(reflexivity) ;
    
    (* EAbs *)
    try(inverts SValue ; specialize (IHe n bs bs1 bs2 (dg_eabs dg v) dgs dgs1 dgs2 H H0 H3) ;
    destruct IHe ; rewrite H1 ; reflexivity ; fail) ;

    (* EFix *)
    try(inverts SValue ; specialize (IHe n bs bs1 bs2 (dg_efix dg v v0) dgs dgs1 dgs2 H H0 H3) ;
    destruct IHe ; rewrite H1 ; reflexivity ; fail).

    (* EApp *)
    inverts SValue.
    destruct bs ; simpl in *|-*.
    apply le_n_0_eq in H ; symmetry in H ; apply max_0 in H ;
    destruct H ; rewrite H, H1 in *|-* ;
    specialize (IHe1 n nil (map_iter_booker e2 bs1 0) 
      (map_iter_booker e2 bs2 0) (dg_eapp_l dg) dgs dgs1 dgs2 Ole) ;
    specialize (IHe2 n nil bs1 bs2 (dg_eapp_r dg) dgs dgs1 dgs2 Ole) ;
    destruct (S.CRaw.svalueb) ;
    simpl in *|-* ; destruct IHe1, IHe2 ; auto ~ ;
    [rewrite H2, H3, H6 | rewrite H2, H6] ; auto ~.

    apply Nat.max_lub_iff in H ; destruct H ;
    specialize (IHe1 n (map_iter_booker e2 (n0::bs) 0) 
    (map_iter_booker e2 bs1 (0+(length (n0::bs))))
    (map_iter_booker e2 bs2 (0+(length (n0::bs)))) (dg_eapp_l dg) dgs dgs1 dgs2) ;
    specialize (IHe2 n (n0::bs) bs1 bs2 (dg_eapp_r dg) dgs dgs1 dgs2 H1) ;
    unfold map_iter_booker in *|-* ;
    rewrite List2Properties.length_map_iter in IHe1 ;
    rewrite <- List2Properties.map_iter_app in IHe1 ;
    rewrite <- List2Properties.map_iter_app in IHe1 ;
    destruct (S.CRaw.svalueb) ;
    simpl in *|-* ; 
    destruct IHe1, IHe2 ; auto ~ ; try(
    destruct (depth e1) ; destruct (depth e2) ; simpl in *|-* ; auto ~ ;
    try(apply Nat.max_lub_iff in H0) ; omega ; fail) ;
    [rewrite H2, H3, H6| rewrite H2, H6] ; auto ~ ; fail.

    (* ERef *)
    try(inverts SValue ; specialize (IHe n bs bs1 bs2 (dg_eref dg) dgs dgs1 dgs2 H H0 H3) ;
    destruct IHe ; rewrite H1 ; reflexivity ; fail).

    (* EDeref *)
    try(inverts SValue ; specialize (IHe n bs bs1 bs2 (dg_ederef dg) dgs dgs1 dgs2 H H0 H3) ;
    destruct IHe ; rewrite H1 ; reflexivity ; fail).

    (* EAssign *)
    inverts SValue.
    destruct bs ; simpl in *|-*.

    apply le_n_0_eq in H ; symmetry in H ; apply max_0 in H ;
    destruct H ; rewrite H, H1 in *|-* ;
    specialize (IHe1 n nil (map_iter_booker e2 bs1 0) 
      (map_iter_booker e2 bs2 0) (dg_eassign_l dg) dgs dgs1 dgs2 Ole) ;
    specialize (IHe2 n nil bs1 bs2 (dg_eassign_r dg) dgs dgs1 dgs2 Ole) ;
    destruct (S.CRaw.svalueb) ;
    simpl in *|-* ; destruct IHe1, IHe2 ; auto ~ ;
    [rewrite H2, H3, H6 | rewrite H2, H6] ; auto ~.

    apply Nat.max_lub_iff in H ; destruct H ;
    specialize (IHe1 n (map_iter_booker e2 (n0::bs) 0) 
    (map_iter_booker e2 bs1 (0+(length (n0::bs))))
    (map_iter_booker e2 bs2 (0+(length (n0::bs)))) (dg_eassign_l dg) dgs dgs1 dgs2) ;
    specialize (IHe2 n (n0::bs) bs1 bs2 (dg_eassign_r dg) dgs dgs1 dgs2 H1) ;
    unfold map_iter_booker in *|-* ;
    rewrite List2Properties.length_map_iter in IHe1 ;
    rewrite <- List2Properties.map_iter_app in IHe1 ;
    rewrite <- List2Properties.map_iter_app in IHe1 ;
    destruct (S.CRaw.svalueb) ;
    simpl in *|-* ; 
    destruct IHe1, IHe2 ; auto ~ ; try(
    destruct (depth e1) ; destruct (depth e2) ; simpl in *|-* ; auto ~ ;
    try(apply Nat.max_lub_iff in H0) ; omega ; fail) ;
    [rewrite H2, H3, H6| rewrite H2, H6] ; auto ~ ; fail.

    (* EBox *)
    assert(depth e <= S (length bs)).
    omega.
    inverts SValue.
    specialize (IHe (S n) (0::bs) bs1 bs2 (dg_ebox dg) (dg::dgs) dgs1 dgs2 H1).
    repeat(rewrite app_comm_cons).
    destruct IHe ; auto ~.
    simpl in *|-*.
    destruct (depth e) ; simpl ; try(omega).
    rewrite H2 ; reflexivity.
    assert(depth e <= S (length bs)).
    omega.
    inverts SValue.
    specialize (IHe (S n) (0::bs) bs1 bs2 (dg_ebox dg) (dg::dgs) dgs1 dgs2 H1).
    repeat(rewrite app_comm_cons).
    destruct IHe ; auto ~.
    destruct (depth e) ; simpl ; try(omega).
    rewrite H2 ; reflexivity.
    
    (* EUnbox *)
    inversion SValue ; subst.
    destruct bs ; simpl in *|-*.
    exfalso ; omega.
    destruct dgs ; simpl in *|-*.
    exfalso ; omega.
    apply le_S_n in H ; apply le_S_n in H0.
    specialize (IHe n0 bs bs1 bs2 d dgs dgs1 dgs2 H H0 H3).
    destruct IHe ; simpl ; try(omega).
    simpl in H1 ; rewrite H1 ; auto ~.

    (* ERun *)
    try(inverts SValue ; specialize (IHe n bs bs1 bs2 (dg_erun dg) dgs dgs1 dgs2 H H0 H3) ;
    destruct IHe ; rewrite H1 ; reflexivity ; fail).

    (* ELift *)
    try(inverts SValue ; specialize (IHe n bs bs1 bs2 (dg_elift dg) dgs dgs1 dgs2 H H0 H3) ;
    destruct IHe ; rewrite H1 ; reflexivity ; fail).
  Qed.

  Lemma trans_depth_0_2:
    forall (e:expr) (bs1 bs2:list nat) (dg:dg_t) (dgs1 dgs2:list dg_t),
    depth e = 0 -> trans e bs1 dg dgs1 = trans e bs2 dg dgs2.
  Proof.
    intros.
    rewrite <- app_nil_l with (l:=bs1).
    rewrite <- app_nil_l with (l:=bs2).
    rewrite <- app_nil_l with (l:=dgs1).
    rewrite <- app_nil_l with (l:=dgs2).
    apply trans_depth_2 ;
    simpl ; omega.
  Qed.

  Lemma phi_depth_0_2:
    forall (v:expr) (bs1 bs2:list nat) (dg:dg_t) (dgs1 dgs2:list dg_t),
    depth v = 0 -> phi v bs1 dg dgs1 = phi v bs2 dg dgs2.
  Proof.
    destruct v ; simpl ; intros ; auto ~.
    rewrite trans_depth_0_2 with (bs2:=bs2) (dgs2:=dgs2) ; auto ~.
    rewrite trans_depth_0_2 with (bs2:=bs2) (dgs2:=dgs2) ; auto ~.
    assert(depth v <= 1).
    omega.
    specialize (trans_depth_2 v (0::nil) bs1 bs2 (dg_ebox dg) (dg::nil) dgs1 dgs2 H0 H0) ; intros.
    simpl in *|-*.
    destruct H1 ; rewrite H1 ; auto ~.
  Qed.

  Lemma trans_memory_depth_0:
    forall (M:Memory.t) (bs1 bs2:list nat),
    memory_depth M = 0 -> trans_mem M bs1 = trans_mem M bs2.
  Proof.
    induction M ; intros.
    reflexivity.
    simpl in *|-*.
    apply max_0 in H ; destruct H.
    rewrite IHM with (bs2:=bs2) ; auto ~.
    rewrite phi_depth_0 with (bs2:=bs2) ; auto ~.
  Qed.

  Lemma booker_depth:
    forall (e:expr) (n:nat),
    depth e <= n -> booker e n = 0.
  Proof.
    induction e ; simpl ; intros ; auto ~.
    apply Nat.max_lub_iff in H.
    destruct H ; rewrite IHe1, IHe2 ; auto ~.
    apply Nat.max_lub_iff in H.
    destruct H ; rewrite IHe1, IHe2 ; auto ~.
    apply IHe ; omega.
    destruct n ; [exfalso ; omega|auto ~].
    apply IHe ; omega.
  Qed.

  Lemma booker_ssubst:
    forall (e v:expr) (m n:nat) (x:var) (ss:StageSet.t),
    depth v = 0 ->
    booker (S.ssubst m ss x e v) n = booker e n.
  Proof.
    induction e ; simpl ; intros ; auto ~.
    destruct (beq_nat x v && CRaw.BindingSet.rho m ss) ; auto ~.
    apply booker_depth ; omega.
    destruct n ; auto ~.
  Qed.

  Lemma map_iter_ssubst:
    forall (bs:list nat) (e v:expr) (m n o:nat) (x:var) (ss:StageSet.t),
    depth v = 0 ->
    List2.map_iter (fun b n => (b + booker (S.ssubst m ss x e v) n)%nat) bs o =
    List2.map_iter (fun b n => (b + booker e n)%nat) bs o.
  Proof.
    induction bs ; simpl ; intros ; auto ~.
    rewrite booker_ssubst ; auto ~.
    rewrite IHbs ; auto ~.
  Qed.

  Lemma booker_le:
    forall (e:S.expr) (m n:nat),
    m <= n -> booker e m = 0 -> booker e n = 0.
  Proof.
    induction e ; simpl ; intros ; auto ~ ;
    try(apply IHe with (m:=m) ; auto ~ ; fail) ;
    try(apply plus_is_O in H0 ; destruct H0 ;
    rewrite IHe1 with (m:=m) ; simpl ; auto ~ ; 
    rewrite IHe2 with (m:=m) ; auto ~ ; fail).
    rewrite IHe with (m:=S m) ; omega.
    destruct n.
    apply le_n_0_eq in H ; subst ; auto ~.
    destruct m ; [inversion H0 |].
    rewrite IHe with (m:=m) ; auto ~.
    omega.
  Qed.

  Definition map_iter_stack (cs:Context.t_stack) (bs:list nat) (n:nat) :=
    List2.map_iter (fun b n => (b+(length (nth n cs nil)))%nat) bs n.

  Lemma booker_length:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    let (_, cs) := trans e bs dg dgs in
    forall (n:nat),
    booker e n = length (nth n cs nil).
  Proof.
    induction e ; simpl ; intros ; 

    (* EConst, EVar, ELoc *)
    try(destruct n ; auto ~ ; fail) ;

    (* EAbs, EFix, ERef, EDeref, ERun, ELift *)
    try(try_specialize_1 IHe bs dg dgs v v0 
    (destruct (trans e) ; intros ; auto ~ ; fail)) ;

    (* EApp, EAssign *)
    try(try_specialize_2 IHe1 (map_iter_booker e2 bs 0) IHe2 bs dg dgs
    (destruct (trans e1) ; destruct (trans e2) ; intros ;
    rewrite ContextStaticProperties.merge_nth ;
    rewrite app_length ;
    rewrite IHe1, IHe2 ; auto ~ ; fail)).

    (* EBox *)
    specialize (IHe (0::bs) (dg_ebox dg) (dg::dgs)).
    destruct (trans e) ; intros.
    destruct t ; intros.
    rewrite booker_le with (m:=n) ; auto ~.
    destruct n ; auto ~.
    rewrite IHe ; auto ~.
    destruct n ; auto ~.
    specialize (IHe (S n)).
    simpl in IHe ; assumption.

    (* EUnbox *)
    destruct (List2.hd_cons bs 0).
    destruct (List2.hd_cons dgs dg_empty).
    specialize (IHe l d l0) ; destruct (trans e) ; intros.
    destruct n0.
    reflexivity.
    simpl.
    apply IHe.
  Qed.

  Lemma map_iter_booker_length:
    forall (e:S.expr) (bs:list nat) (n:nat),
    length (map_iter_booker e bs n) = length bs.
  Proof.
    induction bs ; simpl ; intros ; auto ~.
    unfold map_iter_booker in *|-* ; rewrite IHbs ; auto ~.
  Qed.

  Lemma map_iter_booker_nth:
    forall (e:S.expr) (bs:list nat) (m n:nat),
    nth m (map_iter_booker e bs n) (booker e (m+n)) = 
    (nth m bs 0 + booker e (m+n))%nat.
  Proof.
    intros.
    unfold map_iter_booker.
    specialize (List2Properties.map_iter_nth 
      (fun b n0 : nat => (b + booker e n0)%nat) bs m n 0) ; intros P.
    simpl in P ; rewrite P ; auto ~.
  Qed.

  Lemma map_iter_booker_nth_indep:
    forall (e:S.expr) (bs:list nat) (m n:nat),
    m < length bs ->
    nth m (map_iter_booker e bs n) 0 = 
    (nth m bs 0 + booker e (m+n))%nat.
  Proof.
    intros.
    unfold map_iter_booker.
    specialize (List2Properties.map_iter_nth_indep 
      (fun b n0 : nat => (b + booker e n0)%nat) bs m n 0) ; intros P.
    simpl in P ; rewrite P ; auto ~.
  Qed.

  Lemma map_iter_booker_stack:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    let (_, cs) := trans e bs dg dgs in
    forall n, map_iter_booker e bs n = map_iter_stack cs bs n.
  Proof.
    intros.
    specialize (booker_length e bs dg dgs) ; intros BookerLength.
    destruct (trans e) ; induction bs ; intros ;
    unfold map_iter_booker, map_iter_stack in *|-* ; simpl ; auto ~.
    rewrite BookerLength, IHbs ; auto ~.
  Qed.

  Lemma map_iter_stack_nil:
    forall (bs:list nat) (n:nat),
    map_iter_stack nil bs n = bs.
  Proof.
    induction bs ; simpl ; intros ; auto ~.
    unfold map_iter_stack in *|-* ; simpl ;
    rewrite IHbs ; destruct n ; rewrite plus_0_r ; reflexivity.
  Qed.

  Lemma map_iter_stack_cs:
    forall (bs:list nat) (c:Context.t) (cs:Context.t_stack) (n:nat),
    map_iter_stack (c::cs) bs (S n) = map_iter_stack cs bs n.
  Proof.
    induction bs ; simpl ; intros ; auto ~.
    unfold map_iter_stack in *|-* ; simpl in *|-*.
    rewrite IHbs ; destruct n ; reflexivity.
  Qed.

  Lemma map_iter_stack_bs:
    forall (bs:list nat) (cs:Context.t_stack)  (b:nat) (n:nat),
    map_iter_stack cs (b :: bs) n = 
    (b + length (nth n cs nil))%nat :: map_iter_stack cs bs (S n).
  Proof.
    induction bs ; simpl ; intros ; auto ~.
  Qed.

  Lemma map_iter_stack_nth:
    forall (bs:list nat) (cs:Context.t_stack)  (m n:nat),
    nth m (map_iter_stack cs bs n) (length (nth (m + n) cs nil)) = 
    (nth m bs 0 + length (nth (n+m) cs nil))%nat.
  Proof.
    intros.
    unfold map_iter_stack.
    specialize (List2Properties.map_iter_nth 
      (fun b n0 : nat => (b + length (nth n0 cs nil))%nat) bs m n 0) ; intros P.
    simpl in P ; rewrite P.
    rewrite plus_comm with (m:=m) ; auto ~.
  Qed.

  Lemma map_iter_stack_nth_indep:
    forall (bs:list nat) (cs:Context.t_stack)  (m n:nat),
    m < length bs ->
    nth m (map_iter_stack cs bs n) 0 = 
    (nth m bs 0 + length (nth (n+m) cs nil))%nat.
  Proof.
    intros.
    unfold map_iter_stack.
    specialize (List2Properties.map_iter_nth_indep 
      (fun b n0 : nat => (b + length (nth n0 cs nil))%nat) bs m n 0) ; intros P.
    simpl in P ; rewrite P ; auto ~.
    rewrite plus_comm with (m:=m) ; auto ~.
  Qed.

  Lemma length_h:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    let (_, cs) := trans e bs dg dgs in
    length cs <= length bs ->
    forall (n m:nat) (dg:dg_t),
    let c := nth n cs nil in
    let l := length c in
    let (_, h) := nth m c (M.cast_econst dg 0, (nth n bs 0) + l-m-1) in
    h = (nth n bs 0) + l-m-1.
  Proof.
    assert(forall (m n o p:nat),
      p <= o -> m + n - (o - p) - 1 = m + (p + n) - o - 1) as P1.
    clear ; intros ; omega.

    induction e ; simpl ; intros ;

    (* EConst, EVar, ELoc *)
    try(destruct n ; destruct m ; simpl ; auto ~ ; fail) ;

    (* EAbs, EFix, ERef, EDeref, ERun, ELift *)
    try(try_specialize_1 IHe bs dg dgs v v0 
    (destruct (trans e) ; intros ;
    specialize (IHe H n m dg0) ; assumption ; fail)) ;

    (* EApp, EAssign *)
    try(try_specialize_2 IHe1 (map_iter_booker e2 bs 0) IHe2 bs dg dgs 
    (specialize (booker_length e2 bs (dg_eapp_r dg) dgs) ; intros BookerL1 ;
    specialize (booker_length e2 bs (dg_eassign_r dg) dgs) ; intros BookerL2 ;
    destruct (trans e1) ; destruct (trans e2) ; intros ;
    rewrite ContextStaticProperties.merge_length in H ;
    apply Nat.max_lub_iff in H ; destruct H ;
    specialize (IHe2 H0) ;
    unfold map_iter_booker in IHe1 ;
    rewrite List2Properties.length_map_iter in IHe1 ;
    specialize (IHe1 H) ;
    rewrite ContextStaticProperties.merge_nth ;
    rewrite app_length ;
    specialize (le_lt_dec (length (nth n t nil)) m) ; intros ;
    destruct H1 ; [
    rewrite app_nth2 ; auto ~ ;
    specialize (IHe2 n (m - length (nth n t nil)) dg0) ;
    simpl in IHe2 ;
    rewrite P1 in IHe2 ; auto ~ |] ;
    rewrite app_nth1 ; auto ~ ;
    specialize (IHe1 n m) ;
    unfold map_iter_booker in *|-* ;
    clear IHe2 ;
    specialize (le_lt_dec (length bs) n) ; intros ;
    destruct H1 ; [
    rewrite nth_overflow with (l:=
    (List2.map_iter (fun b n : nat => (b + booker e2 n)%nat) bs 0)) in IHe1 ;
    [rewrite nth_overflow with (l:=bs) ; auto ~ ;
    specialize (IHe1 dg0) ;
    rewrite nth_indep with (d':=(cast_econst dg 0, 0)) in IHe1 ; auto ~ ;
    rewrite nth_indep with (d':=(cast_econst dg 0, 0)) ; auto ~ ;
    rewrite nth_overflow with (l:=t0) ; auto ~ ; [
    rewrite plus_assoc ; simpl ; rewrite plus_0_r ;
    assumption |
    apply le_trans with (m:=length bs) ; auto ~ ] |] ;
    rewrite List2Properties.length_map_iter ;
    assumption |
    specialize (IHe1 dg0) ;
    rewrite nth_indep with (d':=(cast_econst dg0 0, 0)) in IHe1 ; auto ~ ;
    rewrite nth_indep with (d':=(cast_econst dg0 0, 0)) ; auto ~ ;
    specialize(List2Properties.map_iter_nth 
    (fun b n => (b + booker e2 n)%nat) bs n 0 0) ; intros ;
    rewrite nth_indep with (d':=0) in H1 ; auto ~ ; [
    rewrite H1 in IHe1 ; clear H1 ;
    rewrite plus_0_r in IHe1 ;
    rewrite <- plus_comm with (m:=length (nth n t nil)) ;
    rewrite plus_assoc ;
    try(rewrite BookerL1 in IHe1) ; try(rewrite BookerL2 in IHe1) ; auto ~
    | rewrite List2Properties.length_map_iter ; assumption]] ; fail)).

    (* EBox *)
    specialize (IHe (0::bs) (dg_ebox dg) (dg::dgs)) ;
    destruct (trans e).
    destruct t ; intros.
    destruct m ; destruct n ; simpl ; auto ~.
    specialize (le_n_S (length t0) (length bs) H) ; intros.
    specialize (IHe H0 (S n) m dg0).
    simpl in IHe.
    assumption.
    
    (* EUnbox *)
    destruct bs ; simpl.
    destruct (List2.hd_cons dgs dg_empty).
    specialize (IHe nil d l) ;
    destruct (trans e) ; intros.
    simpl in H.
    exfalso ; omega.
    
    destruct (List2.hd_cons dgs dg_empty).
    specialize (IHe bs d l) ;
    destruct (trans e) ; intros.
    simpl in H.
    apply le_S_n in H.
    specialize (IHe H (pred n0) m dg0).
    destruct n0.
    simpl.
    destruct m ; auto ~.
    rewrite <- minus_n_O.
    rewrite plus_minus_n ; auto ~.
    destruct m ; auto ~.
    simpl in *|-*.
    destruct n ; assumption.
  Qed.

  Lemma length_h_match:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    let (_, cs) := trans e bs dg dgs in
    length cs <= length bs ->
    match cs with
    | nil => True
    | cs  => let (c, cs') := Context.shift cs in
      match c with
      | nil => True
      | cons (_, h) c' => h = ((nth (pred (length cs)) bs 0) + length c')%nat
      end
    end.
  Proof.
    intros.
    specialize (length_h e bs dg dgs) ; intros.
    destruct (trans e).
    destruct t ; auto ~.
    specialize (ContextStaticProperties.shift_spec_2 (t::t0)) ; intros.
    simpl length in *|-*.
    simpl pred in *|-*.
    specialize (H H1 (length t0) 0).
    destruct (Context.shift (t::t0)).
    subst.
    destruct (nth (length t0) (t :: t0) nil) ; auto ~.
    simpl in *|-*.
    rewrite <- minus_n_O in H.
    simpl in *|-*.
    rewrite plus_minus in H.
    simpl in *|-*.
    rewrite <- minus_n_O in H.
    specialize (H dg).
    assumption.
    omega.
  Qed.

  Lemma context_mem_length_booker:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    let (_, cs) := trans e bs dg dgs in
    forall (n:nat),
    length (nth n cs nil) = booker e n.
  Proof.
    induction e ; simpl ; intros ; 

    (* EConst, EVar, ELoc *)
    try(destruct n ; auto ~ ; fail) ;

    (* EAbs, EFix, ERef, EDeref, ERun, ELift *)
    try(try_specialize_1 IHe bs dg dgs v v0 
    (destruct (trans e) ; intros ;
    apply IHe ; fail)) ;

    (* EApp, EAssign *)
    try(try_specialize_2 IHe1 (map_iter_booker e2 bs 0) IHe2 bs dg dgs
    (destruct (trans e1) ; destruct (trans e2) ; intros ;
    rewrite ContextStaticProperties.merge_nth ;
    rewrite app_length ;
    rewrite IHe1, IHe2 ; reflexivity ; fail)).

    (* EBox *)
    specialize (IHe (0::bs) (dg_ebox dg) (dg::dgs)).
    destruct (trans e).
    destruct t ; intros ; simpl in *|-*.
    specialize (IHe (S n)) ; destruct n ; auto ~.
    specialize (IHe (S n)) ; simpl in *|-*.
    assumption.
    
    (* EUnbox *)
    destruct (List2.hd_cons bs 0).
    destruct (List2.hd_cons dgs dg_empty).
    specialize (IHe l d l0).
    destruct (trans e) ; intros.
    simpl in *|-*.
    destruct n0 ; auto ~.
  Qed.

  Lemma context_mem_booker:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    let (_, cs) := trans e bs dg dgs in
    forall (n:nat) (v:var),
    n < length bs ->
    VarSet.mem v (Context.context_hole_set (nth n cs nil)) = true ->
    nth n bs 0 <= v < (nth n bs 0) + (booker e n).
  Proof.
    induction e ; simpl ; intros ;
    
    (* EConst, EVar, ELoc *)
    try(destruct n ; inversion H0 ; fail) ;

    (* EAbs, EFix, ERef, EDeref, ERun, ELift *)
    try(try_specialize_1 IHe bs dg dgs v v0 (
    destruct (trans e) ; intros ; apply IHe ; auto ~ ; fail)) ;

    (* EApp, EAssign *)
    try(try_specialize_2 IHe1 (map_iter_booker e2 bs 0) IHe2 bs dg dgs
    (unfold map_iter_booker in *|-* ;
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
    clear IHe1 ; specialize (IHe2 n v H H0) ; omega] ; fail)).

    (* EBox *)
    specialize (IHe (0::bs) (dg_ebox dg) (dg::dgs)).
    destruct (trans e).
    destruct t ; simpl in *|-* ; intros.
    destruct n ; simpl in H0 ; inversion H0.
    apply lt_n_S in H.
    specialize (IHe (S n) v H H0) ; clear H H0 ; simpl in *|-*.
    assumption.
    
    (* EUnbox *)
    destruct bs ; simpl in *|-*.
    destruct (List2.hd_cons dgs dg_empty).
    specialize (IHe nil d l).
    destruct (trans e) ; intros.
    destruct n ; simpl in *|-*.
    rewrite <- VarSetProperties.singleton_equal_add in H0.
    rewrite VarSetProperties.singleton_mem in H0.
    subst ; omega.
    apply lt_S in H ; apply lt_S_n in H.
    specialize (IHe n v H H0) ; clear H H0.
    destruct n ; omega.

    destruct (List2.hd_cons dgs dg_empty).
    specialize (IHe bs d l).
    destruct (trans e) ; intros ; simpl in *|-*.
    destruct n0 ; simpl in *|-*.
    rewrite <- VarSetProperties.singleton_equal_add in H0.
    rewrite VarSetProperties.singleton_mem in H0.
    subst ; omega.
    apply IHe ; auto ~.
    apply lt_S_n in H ; auto ~.
  Qed.

  Lemma context_mem:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    let (_, cs) := trans e bs dg dgs in
    forall (n:nat),
    n < length bs ->
    match nth n cs nil with
    | nil => True
    | (e, v) :: c => VarSet.mem v (Context.context_hole_set c) = false
    end.
  Proof.
    induction e ; intros ; simpl in *|-* ; intros ;

    (* EConst, EVar, ELoc *)
    try(destruct n ; auto ~ ; fail) ;

    (* EAbs, EFix, ERef, EDeref, ERun, ELift *)
    try(try_specialize_1 IHe bs dg dgs v v0 (
    destruct (trans e bs) ; intros ;
    specialize (IHe n H) ;
    assumption ; fail)) ;

    (* EApp, EAssign *)
    try(try_specialize_2 IHe1 (map_iter_booker e2 bs 0) IHe2 bs dg dgs
    (specialize (context_mem_booker e1 (map_iter_booker e2 bs 0) (dg_eapp_l dg) dgs) ;
    intros CMBApp1 ;
    specialize (context_mem_booker e1 (map_iter_booker e2 bs 0) (dg_eassign_l dg) dgs) ;
    intros CMBAssign1 ;
    specialize (context_mem_booker e2 bs (dg_eapp_r dg) dgs) ; intros CMBApp2 ;
    specialize (context_mem_booker e2 bs (dg_eassign_r dg) dgs) ; intros CMBAssign2 ;
    destruct (trans e1) ; destruct (trans e2) ;
    intros ; specialize (IHe1 n) ; specialize (IHe2 n) ;
    rewrite ContextStaticProperties.merge_nth ;
    try(specialize (CMBApp1 n) ; specialize (CMBApp2 n)) ;
    try(specialize (CMBAssign1 n) ; specialize (CMBAssign2 n)) ;
    destruct (nth n t nil) ; simpl ; [
    apply IHe2 ; auto ~ |] ;
    destruct p ;
    rewrite ContextStaticProperties.context_hole_set_app ;
    rewrite VarSetProperties.union_mem ;
    apply orb_false_iff ; 
    unfold map_iter_booker in *|-* ; split ; [
    rewrite List2Properties.length_map_iter in IHe1 ;
    apply IHe1 ; auto ~ |] ;
    rewrite List2Properties.length_map_iter in CMBApp1, CMBAssign1 ;
    remember (VarSet.mem v (Context.context_hole_set (nth n t0 nil))) ;
    symmetry in Heqb ; destruct b ; auto ~ ; exfalso ;
    try(apply CMBApp2 in Heqb ; auto ~ ; clear CMBApp2) ;
    try(apply CMBAssign2 in Heqb ; auto ~ ; clear CMBAssign2) ;
    assert(VarSet.mem v (Context.context_hole_set ((e3, v) :: t1)) = true) ;
    [simpl ; apply VarSetProperties.add_mem_3 |
    try(specialize (CMBApp1 v H H0)) ;
    try(specialize (CMBAssign1 v H H0)) ; clear H0 IHe2 IHe1 ;
    specialize(List2Properties.map_iter_nth_indep 
      (fun b n => (b + booker e2 n)%nat) bs n 0 0 0 H) ; intros ;
    rewrite plus_0_r in H0 ; rewrite H0 in *|-* ; clear H0 ;
    omega] ; fail)).

    (* EBox *)    
    specialize (IHe (0 :: bs) (dg_ebox dg) (dg::dgs)).
    destruct (trans e) ; intros.
    destruct t ; simpl in *|-* ; intros.
    destruct n ; auto ~.
    specialize (IHe (S n)).
    apply IHe ; auto ~.
    apply lt_n_S ; auto ~.

    (* EUnbox *)
    destruct bs ; simpl in *|-*.
    destruct (List2.hd_cons dgs dg_empty).
    specialize (IHe nil d l).
    destruct (trans e nil) ; intros.
    simpl in *|-*.
    destruct n ; auto ~.
    apply IHe ; auto ~ ; omega.

    destruct (List2.hd_cons dgs dg_empty).
    specialize (IHe bs d l).
    destruct (trans e) ; intros.
    simpl in *|-*.
    destruct n0 ; auto ~.
    apply IHe ; auto ~.
    omega.
  Qed.

  Lemma trans_mem_length:
    forall (M:Memory.t) (bs:list nat) (dg:dg_t) (dgs:list dg_t), 
    length (trans_mem M bs dg dgs) = length M.
  Proof.
    induction M ; simpl ; intros ; auto ~.
  Qed.

  Lemma trans_mem_fresh:
    forall (M:Memory.t) (bs:list nat) (dg:dg_t) (dgs:list dg_t), 
    T.Memory.fresh (trans_mem M bs dg dgs) = Memory.fresh M.
  Proof.
    induction M ; simpl ; intros ; auto ~.
  Qed.

  Lemma trans_mem_set:
    forall (M:Memory.t) (l:CRaw.location) (bs:list nat) (dg:dg_t) (dgs:list dg_t) (v:S.expr),
    l <= length M ->
    trans_mem (CRaw.Memory.set l v M) bs dg dgs =
    T.Memory.set l (phi v bs dg dgs) (trans_mem M bs dg dgs).
  Proof.
    induction M ; simpl ; intros.
    apply le_n_0_eq in H ; subst ; auto ~.
    destruct l ; simpl ; auto ~.
    apply le_S_n in H.
    rewrite IHM ; auto ~.
  Qed.

  Lemma trans_mem_get:
    forall (M:Memory.t) (l:CRaw.location) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    l < length M ->
    phi (CRaw.Memory.get l M) bs dg dgs =
    T.Memory.get l (trans_mem M bs dg dgs).
  Proof.
    induction M ; simpl ; intros.
    apply lt_n_O in H ; contradiction.
    destruct l ; simpl ; auto ~.
    apply lt_S_n in H.
    unfold CRaw.Memory.get, T.Memory.get ; simpl.
    specialize (IHM l bs dg dgs H).
    unfold CRaw.Memory.get, T.Memory.get in IHM ; simpl in IHM.
    rewrite IHM ; auto ~.
  Qed.

  Lemma sstep_booker:
    forall (e1 e2:S.expr) (M1 M2:Memory.t),
    memory_depth M1 = 0 ->
    sstep (depth e1) (M1,e1) (M2,e2) ->
    forall (m:nat), S m < (depth e1) ->
    booker e1 m = booker e2 m.
  Proof.
    induction e1 ; simpl ; intros e2 M1 M2 MDepth0 ; intros ;

    (* EConst, EVar, ELoc *)
    try(inversion H ; subst ; auto ~ ; fail) ;

    (* EAbs, EFix *)
    try(inversion H ; subst ; simpl ;
    apply IHe1 with (e2:=e3) (M1:=M1) (M2:=M2) ; rewrite H1 in H3 ; auto ~ ; fail).


    (* EApp *)
    inversion H ; subst.
    specialize (Nat.max_spec (depth e1_1) (depth e1_2)) ; intros Spec1 ;
    destruct Spec1 ; destruct H1 ; rewrite H2 in *|-* ; [
    apply CalculusProperties.depth_sstep_lt in H3 ; [contradiction|omega] |
    simpl ; rewrite IHe1_1 with (e2:=e3) (M1:=M1) (M2:=M2) ; auto ~].

    specialize (Nat.max_spec (depth e1_2) (depth e1_1)) ; intros Spec1 ;
    destruct Spec1 ; destruct H1 ; rewrite Nat.max_comm in H2 ; rewrite H2 in *|-* ; [
    apply CalculusProperties.depth_sstep_lt in H8 ; [contradiction|omega] |
    simpl ; rewrite IHe1_2 with (e2:=e0) (M1:=M1) (M2:=M2) ; auto ~].
    
    simpl in *|-*.
    assert(depth e = 0).
    destruct (depth e) ; destruct (depth e1_2) ; simpl in H1 ; inversion H1 ; auto ~.
    assert(depth e1_2 = 0).
    destruct (depth e) ; destruct (depth e1_2) ; simpl in H1 ; inversion H1 ; auto ~.
    assert(depth (CRaw.ssubst 0 StageSet.empty x e e1_2) = 0).
    specialize (CalculusProperties.depth_ssubst e e1_2 StageSet.empty x 0) ; intros.
    rewrite H2, H4 in H5 ; simpl in H5 ; apply le_n_0_eq in H5 ; auto ~.
    repeat(rewrite booker_depth) ; auto ~ ; try(omega).

    simpl in *|-*.
    assert(depth e = 0).
    destruct (depth e) ; destruct (depth e1_2) ; simpl in H1 ; inversion H1 ; auto ~.
    assert(depth e1_2 = 0).
    destruct (depth e) ; destruct (depth e1_2) ; simpl in H1 ; inversion H1 ; auto ~.
    assert(depth (CRaw.ssubst 0 StageSet.empty f (CRaw.ssubst 0 StageSet.empty x e e1_2)
     (CRaw.EFix f x e)) = 0).
    specialize (CalculusProperties.depth_ssubst (CRaw.ssubst 0 StageSet.empty x e e1_2) (CRaw.EFix f x e) StageSet.empty f 0) ; intros.
    assert(depth (CRaw.ssubst 0 StageSet.empty x e e1_2) = 0).
    specialize (CalculusProperties.depth_ssubst e e1_2 StageSet.empty x 0) ; intros.
    rewrite H2, H4 in H6 ; simpl in H6 ; apply le_n_0_eq in H6 ; auto ~.
    simpl in H5 ; rewrite H2, H6 in H5 ; simpl in H5 ; apply le_n_0_eq in H5 ; auto ~.
    repeat(rewrite booker_depth) ; auto ~ ; try(omega).

    (* ERef *)
    inversion H ; subst.
    apply IHe1 with (m:=m) in H3 ; auto ~.
    simpl ; rewrite booker_depth ; omega.

    (* Deref *)
    inversion H ; subst.
    apply IHe1 with (m:=m) in H3 ; auto ~.
    assert(depth (CRaw.Memory.get l M2) = 0).
    specialize (CalculusProperties.memory_depth_get l M2) ; intros Dpth1.
    rewrite MDepth0 in Dpth1 ; apply le_n_0_eq in Dpth1 ; auto ~.
    simpl ; rewrite booker_depth ; auto ~ ; omega.
    
    (* Assign *)
    inversion H ; subst.

    specialize (Nat.max_spec (depth e1_1) (depth e1_2)) ; intros Spec1 ;
    destruct Spec1 ; destruct H1 ; rewrite H2 in *|-* ; [
    apply CalculusProperties.depth_sstep_lt in H3 ; [contradiction|omega] |
    simpl ; rewrite IHe1_1 with (e2:=e3) (M1:=M1) (M2:=M2) ; auto ~].

    specialize (Nat.max_spec (depth e1_2) (depth e1_1)) ; intros Spec1 ;
    destruct Spec1 ; destruct H1 ; rewrite Nat.max_comm in H2 ; rewrite H2 in *|-* ; [
    apply CalculusProperties.depth_sstep_lt in H8 ; [contradiction|omega] |
    simpl ; rewrite IHe1_2 with (e2:=e0) (M1:=M1) (M2:=M2) ; auto ~].
    
    simpl ; auto ~.
    
    (* EBox *)
    inversion H ; subst.
    assert(S (pred (depth e1)) = depth e1).
    specialize (CalculusProperties.depth_sstep_lt M1 e1 M2 e3 (S (pred (depth e1)))) ; intros.
    destruct (depth e1) ; auto ~.
    apply H1 in H3 ; try(omega) ; contradiction.
    rewrite H1 in H3 ;  simpl ; apply IHe1 with (m:=S m) in H3 ; auto ~ ; omega.

    (* EUnbox *)
    inversion H ; subst.
    simpl ; destruct m ; auto ~.
    apply IHe1 with (m:=m) in H3 ; auto ~ ; omega.
    simpl in *|-*.
    destruct m ; [|exfalso ; omega].
    exfalso ; omega.

    (* ERun *)
    inversion H ; subst.
    apply IHe1 with (m:=m) in H3 ; auto ~.
    simpl in *|-*.
    specialize (booker_depth e2) ; intros.
    destruct (depth e2).
    repeat(rewrite H2) ; auto ~ ; omega.
    destruct n ; simpl in *|-* ; [|inversion H1].
    repeat(rewrite H2) ; auto ~ ; try(omega).
    
    (* ELift *)
    inversion H ; subst.
    apply IHe1 with (m:=m) in H3 ; auto ~.
    simpl in *|-*.
    repeat(rewrite booker_depth) ; auto ~ ; try(omega).
  Qed.

  Lemma map_iter_booker_comm:
    forall (e1 e2:S.expr) (bs:list nat) (m n:nat),
    (map_iter_booker e1 (map_iter_booker e2 bs m) n)
    = (map_iter_booker e2 (map_iter_booker e1 bs n) m).
  Proof.
    induction bs ; simpl ; intros ; auto ~.
    unfold map_iter_booker in *|-* ; simpl.
    rewrite IHbs ; auto ~.
    assert(a + booker e2 m + booker e1 n = a + booker e1 n + booker e2 m)%nat.
    omega.
    rewrite H ; auto ~.
  Qed.

  Lemma map_iter_booker_app:
    forall (e:S.expr) (bs1 bs2:list nat) (n:nat),
    map_iter_booker e (bs1++bs2) n
    = (map_iter_booker e bs1 n) ++ (map_iter_booker e bs2 (length bs1 + n)).
  Proof.
    induction bs1 ; simpl ; intros ; auto ~.
    unfold map_iter_booker in *|-* ; simpl.
    rewrite IHbs1 ; auto ~.
    rewrite <- plus_Snm_nSm ; auto ~.
  Qed.

  Lemma map_iter_booker_hd_cons:
    forall (e:S.expr) (bs:list nat) (b:nat) (n:nat),
    List2.hd_cons (map_iter_booker e (b :: bs) n) 0 =
    ((b + booker e n), map_iter_booker e bs (S n))%nat.
  Proof.
    intros ; reflexivity.
  Qed.

  Lemma sstep_booker_trans:
    forall (e1 e2:S.expr) (M1 M2:Memory.t),
    memory_depth M1 = 0 ->
    sstep (depth e1) (M1,e1) (M2,e2) ->
    forall (e3:S.expr) (bs bs1:list nat) (n:nat),
    depth e3 + n < depth e1 + length bs1 ->
    trans e3 (bs1 ++ (map_iter_booker e1 bs n)) = 
      trans e3 (bs1 ++ (map_iter_booker e2 bs n)) /\
    (svalue 0 e3 -> phi e3 (bs1++(map_iter_booker e1 bs n)) = 
      phi e3 (bs1++(map_iter_booker e2 bs n))).
  Proof.
    intros e1 e2 M1 M2 MDepth0 Step.
    induction e3 ; intros ; simpl ; auto ~ ;

    (* Case EAbs, EFix, ERef, EDEref, ERun, ELift *)
    try(specialize (IHe3 bs bs1 n H) ;
    destruct IHe3 ; rewrite H0 in *|-* ;
    split ; intros ; auto ~ ; fail).

    (* Case EApp *)
    repeat(rewrite map_iter_booker_app) ; auto ~.
    specialize(IHe3_1 (map_iter_booker e3_2 bs (length bs1 + 0)) 
      (map_iter_booker e3_2 bs1 0) n).
    specialize(IHe3_2 bs bs1 n).
    rewrite map_iter_booker_length in *|-*.
    rewrite map_iter_booker_comm with (e1:=e1) in *|-*.
    rewrite map_iter_booker_comm with (e1:=e2) in *|-*.
    simpl in *|-*.
    assert(depth e3_1 + n < depth e1 + length bs1).
    specialize (Nat.max_spec (depth e3_1) (depth e3_2)) ; intros Spec.
    destruct Spec ; omega.
    specialize (IHe3_1 H0) ; clear H0.
    assert(depth e3_2 + n < depth e1 + length bs1).
    specialize (Nat.max_spec (depth e3_1) (depth e3_2)) ; intros Spec.
    destruct Spec ; omega.
    specialize (IHe3_2 H0) ; clear H0.
    destruct IHe3_1 ; destruct IHe3_2.
    rewrite H0, H2 in *|-*.
    split ; intros ; auto ~.
    remember (S.CRaw.svalueb 0 e3_1).
    destruct b ; symmetry in Heqb ; auto ~.
    apply CalculusProperties.svalueb_iff in Heqb.
    specialize (H1  Heqb).
    rewrite H1 ; auto ~.

    
    (* Case EAssign *)
    repeat(rewrite map_iter_booker_app) ; auto ~.
    specialize(IHe3_1 (map_iter_booker e3_2 bs (length bs1 + 0)) 
      (map_iter_booker e3_2 bs1 0) n).
    specialize(IHe3_2 bs bs1 n).
    rewrite map_iter_booker_length in *|-*.
    rewrite map_iter_booker_comm with (e1:=e1) in *|-*.
    rewrite map_iter_booker_comm with (e1:=e2) in *|-*.
    simpl in *|-*.
    assert(depth e3_1 + n < depth e1 + length bs1).
    specialize (Nat.max_spec (depth e3_1) (depth e3_2)) ; intros Spec.
    destruct Spec ; omega.
    specialize (IHe3_1 H0) ; clear H0.
    assert(depth e3_2 + n < depth e1 + length bs1).
    specialize (Nat.max_spec (depth e3_1) (depth e3_2)) ; intros Spec.
    destruct Spec ; omega.
    specialize (IHe3_2 H0) ; clear H0.
    destruct IHe3_1 ; destruct IHe3_2.
    rewrite H0, H2 in *|-*.
    split ; intros ; auto ~.
    remember (S.CRaw.svalueb 0 e3_1).
    destruct b ; symmetry in Heqb ; auto ~.
    apply CalculusProperties.svalueb_iff in Heqb.
    specialize (H1  Heqb).
    rewrite H1 ; auto ~.


    (* Case EBox *)
    repeat(rewrite app_comm_cons).
    specialize (IHe3 bs (0 :: bs1) n).
    simpl in H.
    remember (depth e3).
    destruct n0.
    rewrite trans_depth_0 with (bs2:=((0 :: bs1) ++ map_iter_booker e2 bs n)) ; auto ~.
    simpl in *|-*.
    assert(S (n0 + n) < depth e1 + S (length bs1)).
    omega.
    specialize (IHe3 H0) ; clear H0.
    destruct IHe3 ; rewrite H0 in *|-*.
    split ; intros ; auto ~.

    (* Case EUnbox *)
    destruct bs1 ; simpl in *|-*.
    destruct bs.
    unfold map_iter_booker ; simpl ; split ; intros ; auto ~.
    repeat(rewrite map_iter_booker_hd_cons).
    simpl in *|-*.
    specialize (IHe3 bs nil (S n)).
    simpl in *|-* ; rewrite plus_0_r in *|-*.
    assert(depth e3 + S n < depth e1).
    omega.
    specialize (IHe3 H0) ; clear H0.
    destruct IHe3 ; rewrite H0 in *|-*.
    specialize (sstep_booker e1 e2 M1 M2 MDepth0 Step n) ; intros SBooker.
    rewrite SBooker ; auto ~ ; try(omega).
   
    specialize (IHe3 bs bs1 n).
    assert(depth e3 + n < depth e1 + length bs1).
    omega.
    specialize (IHe3 H0) ; clear H0.
    destruct IHe3 ; rewrite H0 in *|-*.
    split ; intros ; auto ~.
  Qed.


  Lemma sstep_booker_trans_0:
    forall (e1 e2:S.expr) (M1 M2:Memory.t),
    memory_depth M1 = 0 ->
    sstep (depth e1) (M1,e1) (M2,e2) ->
    forall (e3:S.expr) (bs:list nat) (n:nat),
    depth e3 + n < depth e1 ->
    trans e3 (map_iter_booker e1 bs n) = 
      trans e3 (map_iter_booker e2 bs n) /\
    (svalue 0 e3 -> phi e3 (map_iter_booker e1 bs n) = 
      phi e3 (map_iter_booker e2 bs n)).
  Proof.
    intros.
    specialize (sstep_booker_trans e1 e2 M1 M2 H H0 e3 bs nil n).
    simpl in *|-* ; rewrite plus_0_r in *|-*.
    tauto.
  Qed.

End TranslationStaticProperties.

Module TranslationStaticPropertiesImpl (R:Replacement) (S:ReplacementCalculus R)
    (T:StagedCalculus) (M:Monad R S T) (Tr:Translation R S T M).
  Include TranslationStaticProperties R S T M Tr.
End TranslationStaticPropertiesImpl.
