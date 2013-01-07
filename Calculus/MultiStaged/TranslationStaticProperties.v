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

Module ContextStaticProperties (R:Replacement)
  (T:StagedCalculus) (M:Monad R T) (MP:MonadStepProperties R T M).

  Module Context := MP.Translation.Context.
  Import M.
  Import Context.

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
    split ; auto ; try(omega) ;
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
    congr_stack rel (Context.merge cs1 cs2) (Context.merge cs3 cs4).
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
    let (c, cs') := Context.shift cs in
    cs = cs'++ (c::nil).
  Proof.
    induction cs ; intros ; simpl in *|-*.
    exfalso ; omega.
    destruct cs.
    simpl in *|-* ; reflexivity.
    destruct (shift (t0 :: cs)).
    simpl.
    rewrite IHcs ; simpl ; auto.
    omega.
  Qed.

  Lemma shift_spec_2:
    forall (cs:t_stack),
    let (c, _) := Context.shift cs in
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
    Context.unshift cs c = cs ++ (c::nil).
  Proof.
    induction cs ; intros ; simpl in *|-* ; auto.
    rewrite IHcs ; auto.
  Qed.

  Lemma shift_length:
    forall (cs:t_stack),
    let (_, cs') := shift cs in
    length cs' = pred (length cs).
  Proof.
    induction cs ; simpl ; intros ; auto.
    destruct (shift cs).
    destruct cs ; auto.
    simpl in IHcs ; simpl ; auto.
  Qed.

  Lemma context_hole_set_app:
    forall (c1 c2:t),
    Context.context_hole_set (c1 ++ c2) =
    VarSet.union (Context.context_hole_set c1)
    (Context.context_hole_set c2).
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
    induction cs ; auto.
  Qed.

  Lemma merge_nil_l:
    forall (cs:t_stack),
    merge nil cs = cs.
  Proof.
    induction cs ; auto.
  Qed.

  Lemma merge_app:
    forall (cs1 cs2 cs3 cs4:t_stack),
    length cs1 = length cs2 -> 
    merge (cs1++cs3) (cs2++cs4) = (merge cs1 cs2) ++ (merge cs3 cs4).
  Proof.
    induction cs1 ; simpl ; intros.
    destruct cs2 ; [|inversion H] ; auto.
    destruct cs2 ; [inversion H|].
    simpl in H ; inversion H ; subst.
    rewrite <- app_comm_cons.
    rewrite IHcs1 ; auto.
  Qed.

  Lemma shift_merge_1:
    forall (cs1 cs2:t_stack),
    length cs2 < length cs1 ->
    shift (merge cs1 cs2) = let (c1, cs1) := shift cs1 in (c1, merge cs1 cs2).
  Proof.
    induction cs1 ; simpl ; intros.
    destruct cs2 ; auto ; simpl in *|-* ; exfalso ; omega.
    destruct cs2 ; auto ; simpl in *|-*.
    destruct (shift cs1).
    destruct cs1 ; auto.

    rewrite IHcs1 ; auto.
    destruct (shift cs1).
    destruct cs1.
    exfalso ; simpl in *|-* ; omega.
    simpl.
    destruct cs2 ; auto.
    omega.
  Qed.

  Lemma shift_merge_2:
    forall (cs1 cs2:t_stack),
    length cs2 < length cs1 ->
    shift (merge cs2 cs1) = let (c1, cs1) := shift cs1 in (c1, merge cs2 cs1).
  Proof.
    induction cs1 ; simpl ; intros.
    destruct cs2 ; auto ; simpl in *|-* ; exfalso ; omega.
    destruct cs2 ; auto ; simpl in *|-*.
    destruct (shift cs1).
    destruct cs1 ; auto.

    rewrite IHcs1 ; auto.
    destruct (shift cs1).
    destruct cs1.
    exfalso ; simpl in *|-* ; omega.
    simpl.
    destruct cs2 ; auto.
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
    destruct cs2 ; auto ; simpl in *|-* ; exfalso ; omega.
    destruct cs2 ; inversion H ; subst ; auto ; simpl in *|-*.
    rewrite IHcs1 ; auto.
    destruct (shift cs1).
    destruct (shift cs2).
    destruct cs1 ; destruct cs2 ; auto.
    inversion H1 ; subst.
    inversion H1 ; subst.
  Qed.

End ContextStaticProperties.

Module TranslationStaticProperties (R:Replacement) 
    (T:StagedCalculus) (M:Monad R T) (MP:MonadStepProperties R T M).

  Module Translation := MP.Translation.
  Module CalculusProperties := CalculusProperties R M.S.
  Module ContextStaticProperties := ContextStaticProperties R T M MP.
  Import Translation.
  Import M.S.
  Import M.

  Lemma depth_length:
    forall (e:expr) (bs:list nat),
    let (_, cs) := trans e bs in
    depth e = length cs.
  Proof.
    induction e ; simpl ; intros ;
    try(auto ; fail) ;
    try(specialize (IHe bs) ; destruct (trans e bs) ; auto ; fail) ;

    (* EApp, EAssign *)
    try(
    specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ;
    destruct (trans e1) ; 
    destruct (trans e2) ;
    simpl ; rewrite ContextStaticProperties.merge_length ; auto ; fail).
    
    destruct (depth e).
    specialize (IHe (0::bs)).
    destruct (trans e).
    destruct t ; simpl in *|-*.
    reflexivity.
    inversion IHe.

    specialize (IHe (0::bs)).
    destruct (trans e).
    destruct t ; simpl in *|-*.
    inversion IHe.
    inversion IHe.
    reflexivity.

    destruct (List2.hd_cons bs 0).
    specialize (IHe l).
    destruct (trans e).
    simpl.
    auto.
  Qed.

  Lemma length_svalue:
    forall (e:expr) (bs:list nat) (n:nat),
    let (_, cs) := trans e bs in
    length cs < (S n) <-> svalue (S n) e.
  Proof.
    intros.
    specialize (depth_length e) ; intros.
    specialize (H bs).
    destruct (trans e).
    rewrite <- H.
    apply CalculusProperties.depth_svalue.
  Qed.

  Lemma length_sstep:
    forall (e1 e2:expr) (M1 M2:Memory.t) (bs:list nat),
    sstep (depth e1) (M1,e1) (M2,e2) ->
    memory_depth M1 = 0 ->
    let (_, cs2) := trans e2 bs in
    length cs2 <= depth e1.
  Proof.
    intros.
    specialize (CalculusProperties.depth_sstep_eq M1 e1 M2 e2 H0 H) ; intros.
    destruct H1.
    specialize (depth_length e2 bs) ; intros.
    destruct (trans e2).
    rewrite H3 in *|-*.
    assumption.
  Qed.

  Lemma svalue_phi:
    forall (e:expr) (bs:list nat),
    svalue 0 e -> trans_expr e bs = M.ret (phi e bs).
  Proof.
    intros ; inversion H ; subst ; simpl ;
    try(reflexivity) ;
    try(unfold trans_expr ; simpl ; 
    destruct (trans e0) ; reflexivity).

    unfold trans_expr.
    simpl.
    inversion H ; subst.
    specialize (length_svalue e0 (0::bs) 0) ; intros.
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
    forall (e:expr) (bs:list nat),
    let (_, cs) := trans e bs in
    ~ In nil cs.
  Proof.
    induction e ; intros ; simpl ; auto ;

    try(specialize (IHe bs) ; destruct (trans e) ; auto ; fail) ;

    (* EApp, EAssign *)
    try(
    specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ;
    destruct (trans e1) ; destruct (trans e2) ;
    unfold not ; intros ;
    apply context_merge_not_nil in H ;
    tauto ; fail).


    specialize (IHe (0::bs)).
    destruct (trans e).
    destruct t ; simpl.
    tauto.
    unfold not ; intros ; apply IHe.
    simpl ; auto.
    
    destruct (List2.hd_cons bs 0).
    specialize (IHe l).
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
    apply not_or_and in H0 ; destruct H0 ; auto.
    destruct (Context.shift (t :: cs)).
    assert(length (t :: cs) > 0).
    simpl ; omega.
    specialize (IHcs H2 H1).
    destruct IHcs.
    clear H ; split.
    assumption.
    simpl ; apply and_not_or ; auto.
  Qed.

  Lemma admin_context_expr:
    forall (k1 k2:Context.t) (e1 e2:T.expr),
    admin_context k1 k2 -> admin e1 e2 ->
    admin (Context.fill k1 e1) (Context.fill k2 e2).
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
    auto.
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
    apply max_lub_iff in H ; destruct H ;
    specialize (IHe1 (map_iter_booker e2 (n::bs) 0) 
    (map_iter_booker e2 bs1 (0+(length (n::bs))))
    (map_iter_booker e2 bs2 (0+(length (n::bs))))) ;
    specialize (IHe2 (n::bs) bs1 bs2 H0) ;
    unfold map_iter_booker in *|-* ;
    rewrite List2Properties.length_map_iter in IHe1 ;
    rewrite <- List2Properties.map_iter_app in IHe1 ;
    rewrite <- List2Properties.map_iter_app in IHe1 ] ;
    destruct (Translation.S.CRaw.svalueb) ;
    simpl in *|-* ; 
    destruct IHe1, IHe2 ; auto ;
    [rewrite H1, H2, H3| rewrite H1, H3 | 
    rewrite H1, H2, H3| rewrite H1, H3] ; auto ; fail).

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
    destruct v ; simpl ; intros ; auto.
    rewrite trans_depth_0 with (bs2:=bs2) ; auto.
    rewrite trans_depth_0 with (bs2:=bs2) ; auto.
    assert(depth v <= 1).
    omega.
    specialize (trans_depth v (0::nil) bs1 bs2 H0) ; intros.
    simpl in *|-*.
    destruct H1 ; rewrite H1 ; auto.
  Qed.

  Lemma trans_memory_depth_0:
    forall (M:Memory.t) (bs1 bs2:list nat),
    memory_depth M = 0 -> trans_mem M bs1 = trans_mem M bs2.
  Proof.
    induction M ; intros.
    reflexivity.
    simpl in *|-*.
    apply max_0 in H ; destruct H.
    rewrite IHM with (bs2:=bs2) ; auto.
    rewrite phi_depth_0 with (bs2:=bs2) ; auto.
  Qed.

  Lemma booker_depth:
    forall (e:expr) (n:nat),
    depth e <= n -> booker e n = 0.
  Proof.
    induction e ; simpl ; intros ; auto.
    apply max_lub_iff in H.
    destruct H ; rewrite IHe1, IHe2 ; auto.
    apply max_lub_iff in H.
    destruct H ; rewrite IHe1, IHe2 ; auto.
    apply IHe ; omega.
    destruct n ; [exfalso ; omega|auto].
    apply IHe ; omega.
  Qed.

  Lemma booker_ssubst:
    forall (e v:expr) (m n:nat) (x:var) (ss:StageSet.t),
    depth v = 0 ->
    booker (S.ssubst m ss x e v) n = booker e n.
  Proof.
    induction e ; simpl ; intros ; auto.
    destruct (beq_nat x v && CRaw.BindingSet.rho m ss) ; auto.
    apply booker_depth ; omega.
    destruct n ; auto.
  Qed.

  Lemma map_iter_ssubst:
    forall (bs:list nat) (e v:expr) (m n o:nat) (x:var) (ss:StageSet.t),
    depth v = 0 ->
    List2.map_iter (fun b n => (b + booker (S.ssubst m ss x e v) n)%nat) bs o =
    List2.map_iter (fun b n => (b + booker e n)%nat) bs o.
  Proof.
    induction bs ; simpl ; intros ; auto.
    rewrite booker_ssubst ; auto.
    rewrite IHbs ; auto.
  Qed.

  Lemma booker_le:
    forall (e:S.expr) (m n:nat),
    m <= n -> booker e m = 0 -> booker e n = 0.
  Proof.
    induction e ; simpl ; intros ; auto ;
    try(apply IHe with (m:=m) ; auto ; fail) ;
    try(apply plus_is_O in H0 ; destruct H0 ;
    rewrite IHe1 with (m:=m) ; simpl ; auto ; 
    rewrite IHe2 with (m:=m) ; auto ; fail).
    rewrite IHe with (m:=S m) ; omega.
    destruct n.
    apply le_n_0_eq in H ; subst ; auto.
    destruct m ; [inversion H0 |].
    rewrite IHe with (m:=m) ; auto.
    omega.
  Qed.

  Definition map_iter_stack (cs:Context.t_stack) (bs:list nat) (n:nat) :=
    List2.map_iter (fun b n => (b+(length (nth n cs nil)))%nat) bs n.

  Lemma booker_length:
    forall (e:S.expr) (bs:list nat),
    let (_, cs) := trans e bs in
    forall (n:nat),
    booker e n = length (nth n cs nil).
  Proof.
    induction e ; simpl ; intros ; 
    try(destruct n ; auto ; fail) ;
    try(specialize (IHe bs) ;
    destruct (trans e) ; intros ; auto ; fail) ;
    
    try(specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ;
    destruct (trans e1) ; destruct (trans e2) ; intros ;
    rewrite ContextStaticProperties.merge_nth ;
    rewrite app_length ;
    rewrite IHe1, IHe2 ; auto ; fail).

    specialize (IHe (0::bs)).
    destruct (trans e) ; intros.
    destruct t ; intros.
    rewrite booker_le with (m:=n) ; auto.
    destruct n ; auto.
    rewrite IHe ; auto.
    destruct n ; auto.
    specialize (IHe (S n)).
    simpl in IHe ; assumption.

    destruct (List2.hd_cons bs 0).
    specialize (IHe l) ; destruct (trans e) ; intros.
    destruct n0.
    reflexivity.
    simpl.
    apply IHe.
  Qed.

  Lemma map_iter_booker_length:
    forall (e:S.expr) (bs:list nat) (n:nat),
    length (map_iter_booker e bs n) = length bs.
  Proof.
    induction bs ; simpl ; intros ; auto.
    unfold map_iter_booker in *|-* ; rewrite IHbs ; auto.
  Qed.

  Lemma map_iter_booker_stack:
    forall (e:S.expr) (bs:list nat),
    let (_, cs) := trans e bs in
    forall n, map_iter_booker e bs n = map_iter_stack cs bs n.
  Proof.
    intros.
    specialize (booker_length e bs) ; intros BookerLength.
    destruct (trans e) ; induction bs ; intros ;
    unfold map_iter_booker, map_iter_stack in *|-* ; simpl ; auto.
    rewrite BookerLength, IHbs ; auto.
  Qed.

  Lemma map_iter_stack_nil:
    forall (bs:list nat) (n:nat),
    map_iter_stack nil bs n = bs.
  Proof.
    induction bs ; simpl ; intros ; auto.
    unfold map_iter_stack in *|-* ; simpl ;
    rewrite IHbs ; destruct n ; rewrite plus_0_r ; reflexivity.
  Qed.

  Lemma map_iter_stack_cs:
    forall (bs:list nat) (c:Context.t) (cs:Context.t_stack) (n:nat),
    map_iter_stack (c::cs) bs (S n) = map_iter_stack cs bs n.
  Proof.
    induction bs ; simpl ; intros ; auto.
    unfold map_iter_stack in *|-* ; simpl in *|-*.
    rewrite IHbs ; destruct n ; reflexivity.
  Qed.

  Lemma map_iter_stack_bs:
    forall (bs:list nat) (cs:Context.t_stack)  (b:nat) (n:nat),
    map_iter_stack cs (b :: bs) n = 
    (b + length (nth n cs nil))%nat :: map_iter_stack cs bs (S n).
  Proof.
    induction bs ; simpl ; intros ; auto.
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
    rewrite plus_comm with (m:=m) ; auto.
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
    simpl in P ; rewrite P ; auto.
    rewrite plus_comm with (m:=m) ; auto.
  Qed.

  Lemma length_h:
    forall (e:S.expr) (bs:list nat),
    let (_, cs) := trans e bs in
    length cs <= length bs ->
    forall (n m:nat),
    let c := nth n cs nil in
    let l := length c in
    let (_, h) := nth m c (M.cast_econst 0, (nth n bs 0) + l-m-1) in
    h = (nth n bs 0) + l-m-1.
  Proof.
    assert(forall (m n o p:nat),
      p <= o -> m + n - (o - p) - 1 = m + (p + n) - o - 1) as P1.
    clear ; intros ; omega.

    induction e ; simpl ; intros ;

    try(destruct n ; destruct m ; simpl ; auto ; fail) ;

    try(specialize (IHe bs) ; destruct (trans e) ; intros ;
    specialize (IHe H n m) ; assumption ; fail) ;
    
    try(specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ;
    specialize (booker_length e2 bs) ; intros BookerL ;
    destruct (trans e1) ; destruct (trans e2) ; intros ;
    rewrite ContextStaticProperties.merge_length in H ;
    apply max_lub_iff in H ; destruct H ;
    specialize (IHe2 H0) ;
    unfold map_iter_booker in IHe1 ;
    rewrite List2Properties.length_map_iter in IHe1 ;
    specialize (IHe1 H) ;
    rewrite ContextStaticProperties.merge_nth ;
    rewrite app_length ;
    specialize (le_lt_dec (length (nth n t nil)) m) ; intros ;
    destruct H1 ; [
    rewrite app_nth2 ; auto ;
    specialize (IHe2 n (m - length (nth n t nil))) ;
    simpl in IHe2 ;
    rewrite P1 in IHe2 ; auto |] ;
    rewrite app_nth1 ; auto ;
    specialize (IHe1 n m) ;
    unfold map_iter_booker in *|-* ;
    clear IHe2 ;
    specialize (le_lt_dec (length bs) n) ; intros ;
    destruct H1 ; [
    rewrite nth_overflow with (l:=
    (List2.map_iter (fun b n : nat => (b + booker e2 n)%nat) bs 0)) in IHe1 ;
    [rewrite nth_overflow with (l:=bs) ; auto ;
    rewrite nth_indep with (d':=(cast_econst 0, 0)) in IHe1 ; auto ;
    rewrite nth_indep with (d':=(cast_econst 0, 0)) ; auto ;
    rewrite nth_overflow with (l:=t0) ; auto ; [
    rewrite plus_assoc ; simpl ; rewrite plus_0_r ;
    assumption |
    apply le_trans with (m:=length bs) ; auto ] |] ;
    rewrite List2Properties.length_map_iter ;
    assumption |
    rewrite nth_indep with (d':=(cast_econst 0, 0)) in IHe1 ; auto ;
    rewrite nth_indep with (d':=(cast_econst 0, 0)) ; auto ;
    specialize(List2Properties.map_iter_nth 
    (fun b n => (b + booker e2 n)%nat) bs n 0 0) ; intros ;
    rewrite nth_indep with (d':=0) in H1 ; auto ; [
    rewrite H1 in IHe1 ; clear H1 ;
    rewrite plus_0_r in IHe1 ;
    rewrite <- plus_comm with (m:=length (nth n t nil)) ;
    rewrite plus_assoc ;
    rewrite BookerL in IHe1 ; auto
    | rewrite List2Properties.length_map_iter ; assumption]] ; fail).

    (* Case EBox *)
    specialize (IHe (0::bs)) ;
    destruct (trans e).
    destruct t ; intros.
    destruct m ; destruct n ; simpl ; auto.
    specialize (le_n_S (length t0) (length bs) H) ; intros.
    specialize (IHe H0 (S n) m).
    simpl in IHe.
    assumption.
    
    (* Case EUnbox *)
    destruct bs ; simpl.
    specialize (IHe nil) ;
    destruct (trans e) ; intros.
    simpl in H.
    exfalso ; omega.
    
    specialize (IHe bs) ;
    destruct (trans e) ; intros.
    simpl in H.
    apply le_S_n in H.
    specialize (IHe H (pred n0) m).
    destruct n0.
    simpl.
    destruct m ; auto.
    rewrite <- minus_n_O.
    rewrite plus_minus_n ; auto.
    destruct m ; auto.
    simpl in *|-*.
    destruct n ; assumption.
  Qed.

  Lemma length_h_match:
    forall (e:S.expr) (bs:list nat),
    let (_, cs) := trans e bs in
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
    specialize (length_h e bs) ; intros.
    destruct (trans e).
    destruct t ; auto.
    specialize (ContextStaticProperties.shift_spec_2 (t::t0)) ; intros.
    simpl length in *|-*.
    simpl pred in *|-*.
    specialize (H H1 (length t0) 0).
    destruct (Context.shift (t::t0)).
    subst.
    destruct (nth (length t0) (t :: t0) nil) ; auto.
    simpl in *|-*.
    rewrite <- minus_n_O in H.
    simpl in *|-*.
    rewrite plus_minus in H.
    simpl in *|-*.
    rewrite <- minus_n_O in H.
    assumption.
    omega.
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

  Lemma sstep_booker:
    forall (e1 e2:S.expr) (M1 M2:Memory.t),
    memory_depth M1 = 0 ->
    sstep (depth e1) (M1,e1) (M2,e2) ->
    forall (m:nat), S m < (depth e1) ->
    booker e1 m = booker e2 m.
  Proof.
    induction e1 ; simpl ; intros e2 M1 M2 MDepth0 ; intros ;

    (* EConst, EVar, ELoc *)
    try(inversion H ; ssubst ; auto ; fail) ;

    (* EAbs, EFix *)
    try(inversion H ; subst ; simpl ;
    apply IHe1 with (e2:=e3) (M1:=M1) (M2:=M2) ; rewrite H1 in H3 ; auto ; fail).


    (* EApp *)
    inversion H ; subst.
    specialize (max_spec (depth e1_1) (depth e1_2)) ; intros Spec1 ;
    destruct Spec1 ; destruct H1 ; rewrite H2 in *|-* ; [
    apply CalculusProperties.depth_sstep_lt in H3 ; [contradiction|omega] |
    simpl ; rewrite IHe1_1 with (e2:=e3) (M1:=M1) (M2:=M2) ; auto].

    specialize (max_spec (depth e1_2) (depth e1_1)) ; intros Spec1 ;
    destruct Spec1 ; destruct H1 ; rewrite max_comm in H2 ; rewrite H2 in *|-* ; [
    apply CalculusProperties.depth_sstep_lt in H8 ; [contradiction|omega] |
    simpl ; rewrite IHe1_2 with (e2:=e0) (M1:=M1) (M2:=M2) ; auto].
    
    simpl in *|-*.
    assert(depth e = 0).
    destruct (depth e) ; destruct (depth e1_2) ; simpl in H1 ; inversion H1 ; auto.
    assert(depth e1_2 = 0).
    destruct (depth e) ; destruct (depth e1_2) ; simpl in H1 ; inversion H1 ; auto.
    assert(depth (CRaw.ssubst 0 StageSet.empty x e e1_2) = 0).
    specialize (CalculusProperties.depth_ssubst e e1_2 StageSet.empty x 0) ; intros.
    rewrite H2, H4 in H5 ; simpl in H5 ; apply le_n_0_eq in H5 ; auto.
    repeat(rewrite booker_depth) ; auto ; try(omega).

    simpl in *|-*.
    assert(depth e = 0).
    destruct (depth e) ; destruct (depth e1_2) ; simpl in H1 ; inversion H1 ; auto.
    assert(depth e1_2 = 0).
    destruct (depth e) ; destruct (depth e1_2) ; simpl in H1 ; inversion H1 ; auto.
    assert(depth (CRaw.ssubst 0 StageSet.empty f (CRaw.ssubst 0 StageSet.empty x e e1_2)
     (CRaw.EFix f x e)) = 0).
    specialize (CalculusProperties.depth_ssubst (CRaw.ssubst 0 StageSet.empty x e e1_2) (CRaw.EFix f x e) StageSet.empty f 0) ; intros.
    assert(depth (CRaw.ssubst 0 StageSet.empty x e e1_2) = 0).
    specialize (CalculusProperties.depth_ssubst e e1_2 StageSet.empty x 0) ; intros.
    rewrite H2, H4 in H6 ; simpl in H6 ; apply le_n_0_eq in H6 ; auto.
    simpl in H5 ; rewrite H2, H6 in H5 ; simpl in H5 ; apply le_n_0_eq in H5 ; auto.
    repeat(rewrite booker_depth) ; auto ; try(omega).

    (* ERef *)
    inversion H ; subst.
    apply IHe1 with (m:=m) in H3 ; auto.
    simpl ; rewrite booker_depth ; omega.

    (* Deref *)
    inversion H ; subst.
    apply IHe1 with (m:=m) in H3 ; auto.
    assert(depth (CRaw.Memory.get l M2) = 0).
    specialize (CalculusProperties.memory_depth_get l M2) ; intros Dpth1.
    rewrite MDepth0 in Dpth1 ; apply le_n_0_eq in Dpth1 ; auto.
    simpl ; rewrite booker_depth ; auto ; omega.
    
    (* Assign *)
    inversion H ; subst.

    specialize (max_spec (depth e1_1) (depth e1_2)) ; intros Spec1 ;
    destruct Spec1 ; destruct H1 ; rewrite H2 in *|-* ; [
    apply CalculusProperties.depth_sstep_lt in H3 ; [contradiction|omega] |
    simpl ; rewrite IHe1_1 with (e2:=e3) (M1:=M1) (M2:=M2) ; auto].

    specialize (max_spec (depth e1_2) (depth e1_1)) ; intros Spec1 ;
    destruct Spec1 ; destruct H1 ; rewrite max_comm in H2 ; rewrite H2 in *|-* ; [
    apply CalculusProperties.depth_sstep_lt in H8 ; [contradiction|omega] |
    simpl ; rewrite IHe1_2 with (e2:=e0) (M1:=M1) (M2:=M2) ; auto].
    
    simpl ; auto.
    
    (* EBox *)
    inversion H ; subst.
    assert(S (pred (depth e1)) = depth e1).
    specialize (CalculusProperties.depth_sstep_lt M1 e1 M2 e3 (S (pred (depth e1)))) ; intros.
    destruct (depth e1) ; auto.
    apply H1 in H3 ; try(omega) ; contradiction.
    rewrite H1 in H3 ;  simpl ; apply IHe1 with (m:=S m) in H3 ; auto ; omega.

    (* EUnbox *)
    inversion H ; subst.
    simpl ; destruct m ; auto.
    apply IHe1 with (m:=m) in H3 ; auto ; omega.
    simpl in *|-*.
    destruct m ; [|exfalso ; omega].
    exfalso ; omega.

    (* ERun *)
    inversion H ; subst.
    apply IHe1 with (m:=m) in H3 ; auto.
    simpl in *|-*.
    specialize (booker_depth e2) ; intros.
    destruct (depth e2).
    repeat(rewrite H2) ; auto ; omega.
    destruct n ; simpl in *|-* ; [|inversion H1].
    repeat(rewrite H2) ; auto ; try(omega).
    
    (* ELift *)
    inversion H ; subst.
    apply IHe1 with (m:=m) in H3 ; auto.
    simpl in *|-*.
    repeat(rewrite booker_depth) ; auto ; try(omega).
  Qed.

  Lemma map_iter_booker_comm:
    forall (e1 e2:S.expr) (bs:list nat) (m n:nat),
    (map_iter_booker e1 (map_iter_booker e2 bs m) n)
    = (map_iter_booker e2 (map_iter_booker e1 bs n) m).
  Proof.
    induction bs ; simpl ; intros ; auto.
    unfold map_iter_booker in *|-* ; simpl.
    rewrite IHbs ; auto.
    assert(a + booker e2 m + booker e1 n = a + booker e1 n + booker e2 m)%nat.
    omega.
    rewrite H ; auto.
  Qed.

  Lemma map_iter_booker_app:
    forall (e:S.expr) (bs1 bs2:list nat) (n:nat),
    map_iter_booker e (bs1++bs2) n
    = (map_iter_booker e bs1 n) ++ (map_iter_booker e bs2 (length bs1 + n)).
  Proof.
    induction bs1 ; simpl ; intros ; auto.
    unfold map_iter_booker in *|-* ; simpl.
    rewrite IHbs1 ; auto.
    rewrite <- plus_Snm_nSm ; auto.
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
    induction e3 ; intros ; simpl ; auto ;

    (* Case EAbs, EFix, ERef, EDEref, ERun, ELift *)
    try(specialize (IHe3 bs bs1 n H) ;
    destruct IHe3 ; rewrite H0 in *|-* ;
    split ; intros ; auto ; fail).

    (* Case EApp *)
    repeat(rewrite map_iter_booker_app) ; auto.
    specialize(IHe3_1 (map_iter_booker e3_2 bs (length bs1 + 0)) 
      (map_iter_booker e3_2 bs1 0) n).
    specialize(IHe3_2 bs bs1 n).
    rewrite map_iter_booker_length in *|-*.
    rewrite map_iter_booker_comm with (e1:=e1) in *|-*.
    rewrite map_iter_booker_comm with (e1:=e2) in *|-*.
    simpl in *|-*.
    assert(depth e3_1 + n < depth e1 + length bs1).
    specialize (max_spec (depth e3_1) (depth e3_2)) ; intros Spec.
    destruct Spec ; omega.
    specialize (IHe3_1 H0) ; clear H0.
    assert(depth e3_2 + n < depth e1 + length bs1).
    specialize (max_spec (depth e3_1) (depth e3_2)) ; intros Spec.
    destruct Spec ; omega.
    specialize (IHe3_2 H0) ; clear H0.
    destruct IHe3_1 ; destruct IHe3_2.
    rewrite H0, H2 in *|-*.
    split ; intros ; auto.
    remember (S.CRaw.svalueb 0 e3_1).
    destruct b ; symmetry in Heqb ; auto.
    apply CalculusProperties.svalueb_iff in Heqb.
    specialize (H1  Heqb).
    rewrite H1 ; auto.

    
    (* Case EAssign *)
    repeat(rewrite map_iter_booker_app) ; auto.
    specialize(IHe3_1 (map_iter_booker e3_2 bs (length bs1 + 0)) 
      (map_iter_booker e3_2 bs1 0) n).
    specialize(IHe3_2 bs bs1 n).
    rewrite map_iter_booker_length in *|-*.
    rewrite map_iter_booker_comm with (e1:=e1) in *|-*.
    rewrite map_iter_booker_comm with (e1:=e2) in *|-*.
    simpl in *|-*.
    assert(depth e3_1 + n < depth e1 + length bs1).
    specialize (max_spec (depth e3_1) (depth e3_2)) ; intros Spec.
    destruct Spec ; omega.
    specialize (IHe3_1 H0) ; clear H0.
    assert(depth e3_2 + n < depth e1 + length bs1).
    specialize (max_spec (depth e3_1) (depth e3_2)) ; intros Spec.
    destruct Spec ; omega.
    specialize (IHe3_2 H0) ; clear H0.
    destruct IHe3_1 ; destruct IHe3_2.
    rewrite H0, H2 in *|-*.
    split ; intros ; auto.
    remember (S.CRaw.svalueb 0 e3_1).
    destruct b ; symmetry in Heqb ; auto.
    apply CalculusProperties.svalueb_iff in Heqb.
    specialize (H1  Heqb).
    rewrite H1 ; auto.


    (* Case EBox *)
    repeat(rewrite app_comm_cons).
    specialize (IHe3 bs (0 :: bs1) n).
    simpl in H.
    remember (depth e3).
    destruct n0.
    rewrite trans_depth_0 with (bs2:=((0 :: bs1) ++ map_iter_booker e2 bs n)) ; auto.
    simpl in *|-*.
    assert(S (n0 + n) < depth e1 + S (length bs1)).
    omega.
    specialize (IHe3 H0) ; clear H0.
    destruct IHe3 ; rewrite H0 in *|-*.
    split ; intros ; auto.

    (* Case EUnbox *)
    destruct bs1 ; simpl in *|-*.
    destruct bs.
    unfold map_iter_booker ; simpl ; split ; intros ; auto.
    repeat(rewrite map_iter_booker_hd_cons).
    simpl in *|-*.
    specialize (IHe3 bs nil (S n)).
    simpl in *|-* ; rewrite plus_0_r in *|-*.
    assert(depth e3 + S n < depth e1).
    omega.
    specialize (IHe3 H0) ; clear H0.
    destruct IHe3 ; rewrite H0 in *|-*.
    specialize (sstep_booker e1 e2 M1 M2 MDepth0 Step n) ; intros SBooker.
    rewrite SBooker ; auto ; try(omega).
   
    specialize (IHe3 bs bs1 n).
    assert(depth e3 + n < depth e1 + length bs1).
    omega.
    specialize (IHe3 H0) ; clear H0.
    destruct IHe3 ; rewrite H0 in *|-*.
    split ; intros ; auto.
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
