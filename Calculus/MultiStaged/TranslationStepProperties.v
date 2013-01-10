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
Require Import "Calculus/MultiStaged/TranslationStaticProperties".
Require Import "Calculus/MultiStaged/TranslationHoleSubstProperties".

Module ContextProperties (R:Replacement) (T:StagedCalculus) 
    (M:Monad R T) (MP:MonadStepProperties R T M)
    (TrSP:TranslationStaticProperties R T M MP.Translation).

  Module TranslationStaticProperties := TrSP.
  Module StaticProperties := TrSP.ContextStaticProperties.
  Module Context := MP.Translation.Context.
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
  Module TrSP := TranslationStaticPropertiesImpl R T M MP.Translation.
  Module ContextProperties := ContextProperties R T M MP TrSP.
  Module StaticProperties := TrSP.
  Module CalculusProperties := CalculusProperties R M.S.
  Module BindingSetProperties := BindingSetProperties R.
  Module AdminSubstProperties := AdminSubstProperties R T M MP TrSP.
  Module EqSubstProperties3 := AdminSubstProperties.E3.
  Module EqSubstProperties2 := AdminSubstProperties.E2.
  Module EqSubstProperties := AdminSubstProperties.E.
  
  Import EqSubstProperties3.
  Import EqSubstProperties2.
  Import EqSubstProperties.
  Import AdminSubstProperties.
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
    apply Nat.max_lub_iff in H1 ; destruct H1 ; assumption.
    destruct IHe1 ; auto.
    rewrite ContextStaticProperties.merge_length in H1.
    apply Nat.max_lub_iff in H1 ; destruct H1 ; assumption.
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
    apply Nat.max_lub_iff in H1 ; destruct H1 ; assumption.
    destruct IHe1 ; auto.
    rewrite ContextStaticProperties.merge_length in H1.
    apply Nat.max_lub_iff in H1 ; destruct H1 ; assumption.
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
    rewrite H3 ; auto ; remember (MP.Translation.phi) ; simpl in *|-*.
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
      specialize (Nat.max_spec (depth e1_1) (depth e1_2)) ; intros MaxLeft.
      destruct MaxLeft ; destruct H.
      rewrite H0 in H1.
      specialize (CalculusProperties.depth_sstep_lt 
        M1 e1_1 M2 e3 (depth e1_2) H H1) ;
      intros ; contradiction.
      rewrite H0 in *|-* ; clear IHe1_2.
      specialize (IHe1_1 (map_iter_booker e1_2 bs 0) 
        e3 M1 M2 MemSvalue0 MemDepth0).
      assert(length (map_iter_booker e1_2 bs 0) = length bs) as Eq2.
      clear ; unfold map_iter_booker ; 
      rewrite List2Properties.length_map_iter ; auto.
      rewrite Eq2 in IHe1_1 ; specialize (IHe1_1 BSLength H1).
      specialize (depth_length e1_1 (map_iter_booker e1_2 bs 0)) ; intros DpthLength3.
      specialize (depth_length e1_2 bs) ; intros DpthLength4.
      unfold trans_expr ; simpl.
      specialize (CalculusProperties.depth_sstep_eq 
          M1 e1_1 M2 e3 MemDepth0 H1) ; intros Dpth1.
      specialize (eq_ssubst_eq e1_2 bs) ; intros EqSsubstEq1.
      specialize (eq_ssubst_gt e1_2 bs) ; intros EqSsubstEq2.
      specialize (admin_stack_ssubst_merge_1 bs e1_1 e1_2) ; intros AdminSsubst1.
      specialize (admin_stack_ssubst_merge_2 bs e1_1 e1_2) ; intros AdminSsubst2.
      destruct (trans e1_1).
      destruct (trans e1_2).
      destruct t.
 
        (* Case EApp e1 e2, n = 0, e1 -> e1' *)
        destruct t0 ; [|exfalso ; generalize DpthLength3 DpthLength4 H ; clear ; intros ; simpl in *|-* ; omega] ; simpl.
        unfold trans_expr in IHe1_1.
        cases (trans e3 (map_iter_booker e1_2 bs 0)) as e eqn: Transe1.
        inversion IHe1_1 ; subst.
        remember (E.Translation.phi) ; remember (E.Translation.trans) ; simpl in *|-* ; destruct Dpth1 ; subst.
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
        (*cases (Context.merge (t::t1) t0) as t eqn:Merge1.
        assert (Context.merge (t::t1) t0 = 
          Context.merge (t::t1) ((fun x => x) t0)) as Merge1.
          reflexivity.*)
        inversion H.
        
          (* Case depth(e1) = depth(e2) *)
          rewrite ContextStaticProperties.shift_merge_3 ;
          [| rewrite DpthLength4 in H3 ; rewrite DpthLength3 in H3] ; auto.
          cases (Context.merge (t::t1) t0) as t eqn:Merge1.
          simpl in Merge1 ; destruct t0 ; inversion Merge1.
          cases (Context.shift (t :: t1)) as t eqn:Merge2.
          cases (Context.shift t0) as t eqn:Merge3.
          destruct t4 ; [exfalso |] ; auto ; simpl.
          destruct p.
          specialize (svalue_phi e3 (map_iter_booker e1_2 bs 0)) ; 
          intros SValuePhi3 ; unfold trans_expr in SValuePhi3.
          specialize (AdminSsubst1 e3) ; clear AdminSsubst2.
          destruct (trans e3).
          destruct IHe1_1.
          exists x.
          destruct H2 ; split ; auto.
          destruct H4 ; [left|right] ; destruct H4.

            (* Case svalue *)
            destruct H5 ; destruct H6.
            repeat(split) ; auto.
            rewrite Merge1 in AdminSsubst1.
            rewrite ContextStaticProperties.shift_merge_3 in AdminSsubst1.
            rewrite <- Merge2, <- Merge3 in AdminSsubst1.
            specialize (AdminSsubst1 x H2 H6).
            rewrite <- app_comm_cons in AdminSsubst1.
            rewrite H3 in *|-*.
            apply AdminSsubst1 ; auto.
            rewrite DpthLength3, DpthLength4 in H3 ; auto.
            
            remember (S.CRaw.svalueb 0 e1_1).
            destruct b ; symmetry in Heqb.

              (* Case svalue 0 e1_1 *)
              apply CalculusProperties.svalueb_iff in Heqb.
              assert(svalue 0 e3) as SValueE3.
                inversion Heqb ; subst ; 
                try(inversion H1 ; constructor ; fail).
                inversion H1 ; subst ; simpl in H8, H3, Dpth1.
                apply CalculusProperties.depth_svalue in H8.
                clear SValuePhi3 AdminSsubst1 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-*.
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
               (*simpl in *|-*.*)
               unfold map_iter_booker in LengthHMatch.
               assert(S (length t1) <= length
                 (List2.map_iter (fun b n => (b + booker e1_2 n)%nat) bs 0)) as Tmp1.
               rewrite List2Properties.length_map_iter ; auto.
               clear SValuePhi3 AdminSsubst1 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-* ; omega.
               specialize (LengthHMatch Tmp1) ; clear Tmp1.
               unfold map_iter_booker in LengthHMatch.
               specialize (List2Properties.map_iter_nth_indep 
                 (fun b n : nat => (b + booker e1_2 n)%nat)
                 bs (length t1) 0 0 0) ; intros MapIter1.
                 simpl in LengthHMatch ; rewrite MapIter1 in LengthHMatch ; auto.
               subst.
               destruct EqSsubstEq1 with (h:=(nth (length t1) bs 0 + booker e1_2 (length t1 + 0) + length t4)%nat) (v:=(phi x (0 :: nil))) ; auto.
               rewrite H3 ; split ; auto ; rewrite DpthLength3 ; 
               clear SValuePhi3 AdminSsubst1 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-* ; omega.
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
               clear SValuePhi3 AdminSsubst1 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-*.
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
              destruct bs ; [exfalso |] ; 
              clear SValuePhi3 AdminSsubst1 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-* ;
              omega.
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
                 rewrite DpthLength3 in BSLength ; 
                 clear SValuePhi3 AdminSsubst1 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-* ; omega.
              rewrite LengthHMatch in *|-* ; auto ; simpl ; 
              try(rewrite Eq2 ; rewrite DpthLength3 in BSLength ; 
              clear SValuePhi3 AdminSsubst1 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-* ; omega).
              destruct EqSsubstEq1 with (h:=(nth (length t1) (map_iter_booker e1_2 bs 0) 0 + length t4)%nat) 
                (v:=(phi x (0 :: nil))) ; auto.
              rewrite H3 ; clear SValuePhi3 AdminSsubst1 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-* ; omega.
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
              destruct bs ; [exfalso |] ; clear SValuePhi3 AdminSsubst1 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-* ; omega.
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
                 rewrite DpthLength3 in BSLength ; 
                 clear SValuePhi3 AdminSsubst1 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-* ; omega.
              rewrite LengthHMatch in *|-* ; auto ; simpl ; 
              try(rewrite Eq2 ; rewrite DpthLength3 in BSLength ; 
              clear SValuePhi3 AdminSsubst1 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-* ; omega).
              destruct EqSsubstEq1 with (h:=(nth (length t1) (map_iter_booker e1_2 bs 0) 0 + length t4)%nat) 
                (v:=(phi x (0 :: nil))) ; auto.
              rewrite H3 ; clear SValuePhi3 AdminSsubst1 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-* ; omega.
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
          cases (Context.merge (t::t1) t0) as t eqn:Merge1.
          simpl in Merge1 ; destruct t0 ; inversion Merge1.
          cases (Context.shift (t::t1)) as t eqn:Merge2.
          cases (Context.shift t0) as t eqn:Merge3.
          rewrite_eq MP.Translation.trans trans ; rewrite_eq MP.Translation.phi phi.
          destruct t4 ; [exfalso |] ; auto ; simpl.
          destruct p.
          specialize (svalue_phi e3 (map_iter_booker e1_2 bs 0)) ; 
          intros SValuePhi3 ; unfold trans_expr in SValuePhi3.
          specialize (AdminSsubst2 e3) ; clear AdminSsubst1.
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
                inversion H1 ; subst ; 
                clear SValuePhi3 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-*.
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
               (*simpl in *|-*.*)
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
              destruct bs ; [exfalso |] ; clear SValuePhi3 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-* ; omega.
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
              destruct bs ; [exfalso |] ; clear SValuePhi3 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-* ; omega.
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
            rewrite ContextStaticProperties.merge_unshift_1 ; auto.
            specialize (ContextStaticProperties.shift_length (t :: t1)) ; intros L1.
            rewrite <- Merge2 in L1.
            rewrite L1 ; clear SValuePhi3 EqSsubstEq1 EqSsubstEq2 ; simpl in *|-*.
            rewrite DpthLength3, DpthLength4 in *|-*.
            generalize D1 ; clear ; intros.
            apply le_S_n in D1 ; auto.

      (* Case EApp e1 e2,  e2 -> e2' *)
      specialize (Nat.max_spec (depth e1_2) (depth e1_1)) ; intros MaxRight.
      destruct MaxRight ; destruct H ; rewrite Nat.max_comm in H0.
      rewrite H0 in H6.
      specialize (CalculusProperties.depth_sstep_lt 
        M1 e1_2 M2 e0 (depth e1_1) H H6) ;
      intros ; contradiction.
      rewrite H0 in *|-* ; clear IHe1_1.
      specialize (IHe1_2 bs e0 M1 M2 MemSvalue0 MemDepth0 BSLength H6).
      specialize (depth_length e1_1 (map_iter_booker e1_2 bs 0)) ; intros DpthLength3.
      specialize (depth_length e1_2 bs) ; intros DpthLength4.
      specialize (admin_stack_ssubst_merge_3 bs e1_1 e1_2) ; intros AdminSsubst.
      unfold trans_expr ; simpl.
      destruct (trans e1_2).
      destruct t.
 
        (* Case EApp e1 e2, n = 0, e2 -> e2' *)
        rewrite DpthLength4 in H ; apply le_n_0_eq in H.
        rewrite trans_depth_0 with (bs1:=map_iter_booker e0 bs 0) (bs2:=map_iter_booker e1_2 bs 0) ;
        [|generalize H ; clear ; intros ; auto].
        destruct (trans e1_1).
        rewrite_eq MP.Translation.trans trans ; rewrite_eq MP.Translation.phi phi.
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
        specialize (sstep_booker_trans_0 
          e1_2 e0 M1 M2 MemDepth0 H6 e1_1 bs 0) ; intros BKTrans.
        specialize (eq_ssubst_gt e1_1 (map_iter_booker e1_2 bs 0)) ; intros EqSsubstEq.
        specialize (AdminSsubst e0).
        rewrite_eq MP.Translation.trans trans ; rewrite_eq MP.Translation.phi phi.
        destruct (trans e1_1).
        rewrite plus_0_r in *|-*.
        assert(depth e1_1 < depth e1_2) as D1.
        simpl in DpthLength4 ; rewrite DpthLength4 in H2.
        apply CalculusProperties.depth_svalue in H2.
        rewrite <- DpthLength4 in H2 ; auto.
        specialize (BKTrans D1).
        destruct BKTrans as [BKTrans1 BKTrans2].
        rewrite <- BKTrans1 in *|-* ; clear BKTrans1.
        
        

        rewrite ContextStaticProperties.shift_merge_2 ;
        [| rewrite DpthLength3, DpthLength4 in D1 ; auto ; fail].

        cases (Context.merge t1 (t::t0)) as t eqn:Merge1.
        simpl in Merge1 ; destruct t1 ; inversion Merge1.
        cases (Context.shift (t::t0)) as t eqn:Merge2.
        destruct t4 ; [exfalso |] ; auto ; simpl.
        destruct p.
        destruct (trans e0).
        destruct IHe1_2.
        exists x.
        destruct H1 ; split ; auto.
        destruct H3 ; [left|right] ; destruct H3.

          (* Case svalue *)
          destruct H4 ; destruct H5.
          repeat(split) ; auto.
          apply AdminSsubst ; auto.
            
          remember (S.CRaw.svalueb 0 e1_1).
          destruct b ; symmetry in Heqb.

          (* Case svalue 0 e1_1 *)
          apply CalculusProperties.svalueb_iff in Heqb.
          unfold admin_ssubst ; intros.
          rewrite <- BKTrans2 ; auto.
          rewrite MP.ssubst_bind with (f2:=
            fun v2 => cast_eapp (ssubst (depth e1_2)
               match depth e1_2 with
               | 0 => ss | 1 => ss
               | S (S n) =>
                 if ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))
                 then StageSet.add (S n) ss else ss
                 end (cast_var (hole_var v))
                 (phi e1_1 (map_iter_booker e1_2 bs 0)) (phi x (0 :: nil)))
               v2) ; auto.
          constructor ; auto.
          (*simpl in *|-*.*)
          destruct H7 ; unfold admin_ssubst in H7.
          remember (ltb v (nth 0 bs 0 + booker e1_2 0)).
          destruct b ; symmetry in Heqb0.
          assert(ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0)) = true) as True1.
                 apply leb_iff ; apply leb_iff in Heqb0 ; omega.
          destruct (depth e1_2) ; try(apply H7 ; auto ; try(omega) ; constructor).
          destruct n ; try(apply H7 ; auto ; try(omega) ; constructor).
          rewrite True1 ; apply H7 ; auto.
          destruct (depth e1_2) ; try(apply H7 ; auto).
          destruct n ; try(apply H7 ; auto).
          destruct (ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))) ; auto.
          rewrite StageSetProperties.add_mem_4 ; auto.
          destruct (ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))) ; auto.
          rewrite <- StageSetProperties.ub_le_1 ; auto.

          intros.
          destruct EqSsubstEq with (m:=depth e1_2) (h:=v) (v:=(phi x (0 :: nil))) ; auto.
          rewrite map_iter_booker_length ; omega.
          destruct H11 ; specialize (H12 Heqb).
          unfold eq_ssubst in H12.
          destruct (depth e1_2) ; try(rewrite H12 ; auto ; try(omega) ; constructor).
          destruct n ; try(rewrite H12 ; auto ; try(omega) ; constructor).
          assert((nth 0 (map_iter_booker e1_2 bs 0) 0 + booker e1_1 0) =
           (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0)))%nat as Eq1.
          rewrite map_iter_booker_nth_indep ; simpl ; try(omega).
          rewrite <- Eq1, H12 ; auto ; constructor.

          intros ; rewrite MP.ssubst_eapp ; auto.

          (* Case not svalue 0 e1_1 *)
          unfold admin_ssubst ; intros.
          rewrite MP.ssubst_bind with (f2:=(fun v1 : T.expr => bind
            (ssubst (depth e1_2)
            match depth e1_2 with
              | 0 => ss | 1 => ss
              | S (S n) => if ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))
              then StageSet.add (S n) ss else ss  end (cast_var (hole_var v)) e (phi x (0 :: nil)))
            (fun v2 : T.expr => cast_eapp v1 v2))).
          
          constructor ; auto.
          destruct EqSsubstEq with (m:=depth e1_2) (h:=v) (v:=(phi x (0 :: nil))) ; auto.
          rewrite map_iter_booker_length ; omega.
          unfold eq_ssubst in H10.
          destruct (depth e1_2) ; try(rewrite H10 ; auto ; try(omega) ; constructor).
          destruct n ; try(rewrite H10 ; auto ; try(omega) ; constructor).
          assert((nth 0 (map_iter_booker e1_2 bs 0) 0 + booker e1_1 0) =
           (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0)))%nat as Eq1.
          rewrite map_iter_booker_nth_indep ; simpl ; try(omega).
          rewrite <- Eq1, H10 ; auto ; constructor.

          intros ; constructor ; auto ; [|intros ; constructor].
          destruct H7 ; unfold admin_ssubst in H7.
          destruct (depth e1_2) ; try(apply H7 ; auto ; omega).
          destruct n ; try(apply H7 ; auto ; omega).
          remember (ltb v (nth 0 bs 0 + booker e1_2 0)).
          destruct b ; symmetry in Heqb0.
          assert(ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0)) = true) as True1.
                 apply leb_iff ; apply leb_iff in Heqb0 ; omega.
          rewrite True1 ; apply H7 ; auto.
          apply H7 ; auto.
          destruct (ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))) ; auto.
          rewrite StageSetProperties.add_mem_4 ; auto.
          destruct (ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))) ; auto.
          rewrite <- StageSetProperties.ub_le_1 ; auto.

          intros.
          rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr =>
            cast_eapp (ssubst (depth e1_2)
            match depth e1_2 with
              | 0 => ss | 1 => ss
              | S (S n) => if ltb v (nth 0 bs 0 + (booker e1_1 0 + booker e1_2 0))
              then StageSet.add (S n) ss else ss  end (cast_var (hole_var v)) v2 (phi x (0 :: nil))) v0)) ; auto.
          intros ; rewrite MP.ssubst_eapp ; auto.

          (* patch *)
          intros SV ; inversion SV.
          

          (* Case not svalue *)
          exists x0.
          destruct H3 ; destruct H4 ; destruct H5 ; 
          destruct H7 ; subst ; repeat(split) ; auto.
          remember (S.CRaw.svalueb 0 e1_1).
          destruct b ; symmetry in Heqb ; auto.
          apply CalculusProperties.svalueb_iff in Heqb.
          rewrite BKTrans2 ; auto.
          intros ; rewrite H7 ; auto.
          unfold trans_expr ; destruct (trans x0).
          simpl.
          rewrite ContextStaticProperties.merge_unshift_2 ; auto.
          specialize (ContextStaticProperties.shift_length (t :: t0)) ; intros L1.
          rewrite <- Merge2 in L1.
          rewrite L1 ; clear AdminSsubst EqSsubstEq BKTrans2 ; simpl in *|-*.
          rewrite DpthLength3, DpthLength4 in *|-*.
          generalize D1 ; clear ; intros.
          apply le_S_n in D1 ; auto.

      (* Case EApp (EAbs), n = 0 *)
      symmetry in H ; apply max_0 in H.
      destruct H.
      clear IHe1_2 IHe1_1.
      specialize (svalue_phi (CRaw.EAbs x e) (map_iter_booker e1_2 bs 0)) ; intros SValuePhi1.
      specialize (depth_length e (map_iter_booker e1_2 bs 0)) ; intros DpthLength1.
      unfold trans_expr in SValuePhi1.
      rewrite_eq MP.Translation.trans trans ; 
      rewrite_eq MP.Translation.phi phi ;
      simpl in SValuePhi1.
      specialize (trans_ssubst_source e e1_2 bs x StageSet.empty 0) ; intros TSS.
      rewrite trans_depth_0 with (bs2:=(map_iter_booker e1_2 bs 0)) in TSS ; 
      rewrite_eq MP.Translation.trans trans ; rewrite_eq MP.Translation.phi phi ; auto.
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
      unfold trans_expr ; 
      rewrite_eq MP.Translation.trans trans ; rewrite_eq MP.Translation.phi phi ; 
      rewrite H2 ; auto.
      apply MP.astep_app_abs ; auto.
      constructor.

      (* Case EApp (EFix), n = 0 *)
      symmetry in H ; apply max_0 in H.
      destruct H.
      clear IHe1_2 IHe1_1.
      specialize (svalue_phi (CRaw.EFix f x e) (map_iter_booker e1_2 bs 0)) ; intros SValuePhi1.
      specialize (depth_length e (map_iter_booker e1_2 bs 0)) ; intros DpthLength1.
      unfold trans_expr in SValuePhi1 ; 
      rewrite_eq MP.Translation.trans trans ; rewrite_eq MP.Translation.phi phi ; simpl trans in SValuePhi1 ;
      specialize (trans_ssubst_source e e1_2 bs x StageSet.empty 0) ; intros Ssubst2.
      specialize (trans_ssubst_source (S.ssubst 0 StageSet.empty x e e1_2) 
        (CRaw.EFix f x e) bs f StageSet.empty 0) ; intros Ssubst1.
      simpl in Ssubst1.
      rewrite trans_depth_0 with (e:=e) (bs2:=(map_iter_booker e1_2 bs 0)) in Ssubst1 ; auto.
      rewrite trans_depth_0 with (bs2:=(map_iter_booker e1_2 bs 0)) in Ssubst2 ; 
      rewrite_eq MP.Translation.trans trans ; rewrite_eq MP.Translation.phi phi ;auto.
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
      rewrite_eq MP.Translation.trans trans ; rewrite_eq MP.Translation.phi phi ;
      rewrite trans_mem_get ; auto.
      apply MP.astep_ederef ; auto.
      rewrite trans_mem_length ; auto.
      rewrite_eq MP.Translation.trans trans ; rewrite_eq MP.Translation.phi phi ;
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
    rewrite_eq MP.Translation.trans trans ; rewrite_eq MP.Translation.phi phi ;
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
            rewrite_eq MP.Translation.phi phi ;
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
        cases (Context.shift (t0 :: t1)) as t eqn:Shift1.
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
          rewrite_eq E.Translation.Context.fill Context.fill ;
          rewrite_eq E.Translation.booker booker.
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
    cases (trans e1 bs) as e eqn:TransE1.
    inversion Step ; subst.

      (* Case EUnbox -> EUnbox *)
      apply le_S_n in BSLength.
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      specialize (depth_length e3 bs) ; intros DpthLength2.
      specialize (CalculusProperties.depth_sstep_eq M1 e1 M2 e3 MemDepth0 H1) ; 
      intros DpthStep ; simpl.
      destruct t.

        (* Case n = 1 *)
        unfold trans_expr in *|-* ;
        rewrite_eq MP.Translation.trans trans ; rewrite_eq MP.Translation.phi phi ;
        simpl in *|-*.
        cases (trans e3 bs) as e eqn:TransE3.
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
        rewrite_eq MP.Translation.trans trans ; rewrite_eq MP.Translation.phi phi ;
        cases (Context.shift (t :: t0)) as t eqn:Shift1.
        destruct t1 ; simpl in *|-*.
        assumption.
        destruct p ; cases (trans e3 bs) as e eqn:TransE3.
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
          apply ContextStaticProperties.CongrCSubst_cons with (u1:=e) (u2:=e2) (c1:=nil)  
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
          apply ContextStaticProperties.CongrCSubst_cons with (u1:=e) (u2:=e2) (c1:=nil)  
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
          apply ContextStaticProperties.CongrCSubst_cons with (u1:=e) (u2:=e2) (c1:=nil)  
            (c2:=nil) (n:=depth e1) (v:=(phi x (0 :: nil)))
            (b1:=n0) (b2:=n) ; auto.
          destruct t0 ; [inversion Shift1 |].
          destruct (Context.shift (t0 :: t2)) ; inversion Shift1 ; subst.
          assumption.
          constructor ; auto.
          constructor ; auto.

          cases (Context.unshift t2 (p :: t1)) as t eqn:Shift2.
          destruct t2 ; simpl in Shift2 ; inversion Shift2.
          inversion H3 ; subst.
          constructor ; auto.
          assert(forall e:T.expr, (e,n) = (e, n + (length (tl (0::nil)))))%nat as Tmp1.
          simpl ; rewrite plus_0_r ; reflexivity.
          simpl tl in Tmp1.
          rewrite Tmp1.
          rewrite Tmp1.
          
          apply ContextStaticProperties.CongrCSubst_cons with (u1:=e) (u2:=e2) (c1:=nil)  
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
          
          apply ContextStaticProperties.CongrCSubst_cons with (u1:=e) (u2:=e2) (c1:=nil)  
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
      assert((let (e8, _) := trans e2 (0::bs) in e8) = trans_expr e2 (0::bs)) as TransExpr.
      unfold trans_expr ; reflexivity.
      cases (trans e2 (0::bs)) as e eqn:TransE3.
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
      rewrite_eq MP.Translation.trans trans ; rewrite_eq MP.Translation.phi phi ;
      simpl in *|-*.
      specialize (depth_length e2 (0::bs)) ; intros DpthLength2.
      specialize (length_svalue e2 (0::bs)) ; intros SValueLength.
      specialize (svalue_phi (CRaw.EBox e2) bs) ; intros SValuePhi.
      unfold trans_expr in SValuePhi ; simpl trans_expr in *|-*.
      rewrite_eq MP.Translation.trans trans ; rewrite_eq MP.Translation.phi phi ;
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
      rewrite trans_depth_0 with (bs1:=0::bs) (bs2:=bs) ; 
      rewrite_eq MP.Translation.trans trans ; rewrite_eq MP.Translation.phi phi ;
      auto.
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
