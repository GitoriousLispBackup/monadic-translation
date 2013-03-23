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
Require Import "Calculus/MultiStaged/DataGathering".

Definition ltb (m n:nat) := leb (S m) n.

Module EqSubstProperties3 (R:Replacement) (S:ReplacementCalculus R)
    (T:StagedCalculus) (DG:DataGathering R S) 
    (DGP:DataGatheringPredicates R S DG)
    (DGR:DataGatheringRequirements R S DG DGP)
    (M:Monad R S T DG) (MP:MonadStepProperties R S T DG DGP DGR M) 
    (TrSP:TranslationStaticProperties R S T DG DGP DGR M MP.Translation).

  Module Translation := MP.Translation.
  Module StaticProperties := TrSP.
  Module ContextStaticProperties := TrSP.ContextStaticProperties.
  Module CalculusProperties := CalculusProperties R S.
  Module BindingSetProperties := BindingSetProperties R S.CRaw.BindingSet.
  Import StaticProperties.
  Import Translation.
  Import S.
  Import M.
  Import DG.

  Definition eq_ssubst_3 (n:nat) (h:CRaw.var) 
      (m:nat) (v:T.expr) (b:nat) (u1 u2:T.expr) : Prop :=
      forall (ss:StageSet.t),
      StageSet.ub n ss = true ->
      (M.ssubst n (match n with
	  | S (S n) => if ltb h (b + m) && leb b h
       		then StageSet.add (S n) ss else ss
	  | _ => ss
          end) (M.cast_var (hole_var h)) u1 v) = u2.

  Definition eq_context_ssubst_3 := ContextStaticProperties.congr_context_ssubst eq_ssubst_3.
  Definition eq_stack_ssubst_3 := ContextStaticProperties.congr_stack_ssubst eq_ssubst_3.

  Lemma eq_ssubst_3_h_lt:
    forall (e:T.expr) (b1 b2:nat) (h:S.var) (v:T.expr) (n m1 m2:nat),
    eq_ssubst_3 n h m1 v b1 e e -> h < b1 ->
    eq_ssubst_3 n h m2 v b2 e e.
  Proof.
    unfold eq_ssubst_3 ; intros ; auto ~.
    assert(leb b1 h = false) as False1.
    apply leb_iff_conv ; omega.
    rewrite False1, andb_false_r in H.
    destruct n ; [rewrite H ; auto ~|].
    destruct n ; [rewrite H ; auto ~|].
    rewrite H ; auto ~.
    destruct (ltb h (b2 + m2) && leb b2 h) ; auto ~.
    rewrite <- StageSetProperties.ub_le_1 ; auto ~.
  Qed.

  Lemma eq_context_ssubst_3_h_lt:
    forall (c:Context.t) (b1 b2 b3:nat) (h:S.var) (v:T.expr) (n m1 m2:nat),
    eq_context_ssubst_3 n h m1 v b1 b2 c c -> 
    h < b1 -> eq_context_ssubst_3 n h m2 v b3 b2 c c.
  Proof.
    induction c ; intros ; auto ~.
    constructor.
    inversion H ; subst.
    constructor ; auto ~.
    apply eq_ssubst_3_h_lt with (b1:=b1) (m1:=m1) ; auto ~.
    apply IHc with (b1:=b1) (m1:=m1) ; auto ~.
  Qed.

  Lemma eq_ssubst_3_m_Sm:
    forall (e:T.expr) (b:nat) (h:S.var) (v:T.expr) (n m:nat),
    eq_ssubst_3 n h m v b e e -> eq_ssubst_3 n h (S m) v b e e.
  Proof.
    unfold eq_ssubst_3 ; intros.
    case_beq_nat h (b + m)%nat.
    assert(ltb (b+m)%nat (b + m)%nat = false) as LtbFalse.
    apply leb_iff_conv ; omega.
    rewrite LtbFalse in H ; simpl in H.
    assert(ltb (b+m)%nat (b + S m)%nat = true) as LtbTrue.
    apply leb_iff ; omega.
    rewrite LtbTrue ; simpl.
    destruct n.
    apply H ; auto ~.
    destruct n ; apply H ; destruct (leb b (b + m)) ; auto ~.
    rewrite <- StageSetProperties.ub_le_1 ; auto ~.
    assert(ltb h (b + S m) = ltb h (b + m)) as Eq1.
    generalize E ; clear ; intros.
    remember (ltb h (b + m)) ; destruct b0 ; symmetry in Heqb0 ;
    [apply leb_iff ; apply leb_iff in Heqb0 | 
    apply leb_iff_conv ; apply leb_iff_conv in Heqb0] ; omega.
    rewrite Eq1 ; apply H ; auto ~.
  Qed.

  Lemma eq_ssubst_3_m_ge:
    forall (e:T.expr) (b:nat) (h:S.var) (v:T.expr) (n m p:nat),
    eq_ssubst_3 n h m v b e e -> 
    m <= p -> eq_ssubst_3 n h p v b e e.
  Proof.
    intros.
    induction H0 ; auto ~.
    apply eq_ssubst_3_m_Sm ; auto ~.
  Qed.

  Lemma eq_context_ssubst_3_m_ge:
    forall (c:Context.t) (b1 b2:nat) (h:S.var) (v:T.expr) (n m p:nat),
    eq_context_ssubst_3 n h m v b1 b2 c c -> 
    m <= p -> eq_context_ssubst_3 n h p v b1 b2 c c.
  Proof.
    intros.
    induction c ; auto ~.
    constructor.
    inversion H ; subst.
    constructor ; auto ~.
    apply eq_ssubst_3_m_ge with (m:=m) ; auto ~.
    apply IHc ; auto ~.
  Qed.

  Lemma eq_ssubst_3_fill_gt_1_strong:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) (dg_ebox dg) (dg::dgs) in
    match cs with
    | c1 :: nil => 
      match c1 with
      | nil => False
      | _ => forall (m:nat), 
        0 < m < length bs ->
        let b := hd 0 bs in
        eq_context_ssubst_3 m h 0 v b 0 c1 c1 ->
        forall (ss:StageSet.t),
        StageSet.ub m ss = true ->
        (M.ssubst (S m) (match (S m) with
	  | S (S m) => if ltb h (length c1) && leb 0 h
       		then StageSet.add (S m) 
                (match m with
                | 0 => ss
                | S m0 =>
                    if ltb h (b + 0) && leb (hd 0 bs) h then StageSet.add (S m0) ss else ss
                end)
                else 
                (match m with
                | 0 => ss
                | S m0 =>
                    if ltb h (b + 0) && leb (hd 0 bs) h then StageSet.add (S m0) ss else ss
                end)
	  | _ => (match m with
                | 0 => ss
                | S m0 =>
                    if ltb h (b + 0) && leb (hd 0 bs) h then StageSet.add (S m0) ss else ss
                end)
          end) (M.cast_var (hole_var h)) e0 v) = e0 ->
        (M.ssubst m (match m with
	  | S (S m) => if ltb h (b + 0) && leb (hd 0 bs) h
       		then StageSet.add (S m) ss else ss
	  | _ => ss
          end) (M.cast_var (hole_var h)) (Context.fill dg c1 (ret dg (cast_ebox dg e0))) v) = 
          (Context.fill dg c1 (ret dg (cast_ebox dg e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (context_stack_not_nil e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros CSNotNil.
    destruct (trans e (0::bs) (dg_ebox dg) (dg::dgs)).
    destruct t ; auto ~.
    destruct t0 ; auto ~.
    destruct t ; auto ~.
    exfalso ; apply CSNotNil ; simpl ; auto ~.
    simpl ; rewrite andb_true_r in *|-* ; intros.

    simpl in *|-*.
    inversion H0.
    subst c1 u2 c2 p.
    clear H0 CSNotNil.
    destruct bs ; [exfalso ; generalize H ; clear ; simpl ; intros ; omega|].
    simpl in *|-*.
    generalize dependent u1 ; generalize dependent ss.
    induction t ; simpl ; unfold eq_ssubst_3 ; intros.

    destruct m ; [exfalso ; omega|].
    rewrite MP.ssubst_bind with (f2:=
    (fun v0 : T.expr =>
      cast_eapp dg (cast_eabs dg (cast_var (hole_var 0)) (ret dg (cast_ebox dg e0))) v0)).
    rewrite H6 ; auto ~.
    intros.
    rewrite MP.ssubst_eapp, MP.ssubst_eabs, MP.ssubst_ret, MP.ssubst_ebox.
    simpl in *|-*.

    assert(beq_var (hole_var h) (hole_var 0) = ltb h 1) as Eq1.
    clear ; simpl ; remember (ltb h 1) ; destruct b ; symmetry in Heqb.
    apply beq_nat_true_iff ; apply leb_iff in Heqb ; unfold hole_var ; omega.
    apply beq_nat_false_iff ; apply leb_iff_conv in Heqb ; unfold hole_var ; omega.
    destruct m ; destruct (ltb h (n + 0) && leb n h) ; simpl in *|-* ; 
    rewrite Eq1, H2 ; auto ~.

    inversion H8 ; clear H8.
    subst c1 u2 c2 a.
    destruct m ; [exfalso ; omega|].

    rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr =>
     cast_eapp dg
     (cast_eabs dg (cast_var (hole_var (S (length t))))
        (bind dg u0
           (fun v1 : T.expr =>
            cast_eapp dg
              (cast_eabs dg (cast_var (hole_var (length t)))
                 (Context.fill dg t (ret dg (cast_ebox dg e0)))) v1))) v0)).
    rewrite H6 ; auto ~.
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
      destruct m ; [| destruct (ltb (S (length t)) (n + 0) && leb n (S (length t))) ] ;
      try(rewrite StageSetProperties.add_add) ; rewrite IHt ; auto ~ ;
      try(rewrite StageSetProperties.add_mem_4 ; auto ~) ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto ~).
      rewrite StageSetProperties.add_add ; auto ~.

      (* Case h < S length t *)
      assert(beq_var (hole_var h) (hole_var (S (length t))) = false) as False1.
      apply beq_nat_false_iff ; unfold hole_var ; omega.
      rewrite False1, IHt ; auto ~.
      assert(ltb h (S (length t)) = ltb h (S (S (length t)))) as Eq1.
      remember (ltb h (S (S (length t)))) ; destruct b ; symmetry in Heqb.
      apply leb_iff ; apply leb_iff in Heqb ; omega.
      apply leb_iff_conv ; apply leb_iff_conv in Heqb ; omega.
      rewrite Eq1 ; auto ~.
  Qed.

  Lemma eq_ssubst_3_fill_gt_1:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) (dg_ebox dg) (dg::dgs) in
    match cs with
    | c1 :: nil => 
      match c1 with
      | nil => False
      | _ => forall (m:nat), 
        0 < m < length bs ->
        let b := hd 0 bs in
        eq_ssubst_3 (S m) h (length c1) v 0 e0 e0 ->
        eq_context_ssubst_3 m h 0 v b 0 c1 c1 ->
        eq_ssubst_3 m h 0 v b
        (Context.fill dg c1 (ret dg (cast_ebox dg e0))) 
        (Context.fill dg c1 (ret dg (cast_ebox dg e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (eq_ssubst_3_fill_gt_1_strong e bs dg dgs) ; intros Strong1.
    destruct (trans e (0::bs) (dg_ebox dg) (dg::dgs)).
    destruct t ; auto ~.
    destruct t0 ; auto ~.
    destruct t ; auto ~.
    unfold eq_ssubst_3 ; intros.
    apply Strong1 ; auto ~.
    simpl plus in *|-* ; simpl length in *|-*.
    destruct m.
    apply H0 ; auto ~.
    rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto ~.
    destruct m.
    apply H0 ; auto ~.
    rewrite StageSetProperties.ub_le_2 with (m:=1) ; auto ~.
    apply H0 ; auto ~.
    destruct (ltb h (hd 0 bs + 0) && leb (hd 0 bs) h) ; [
    rewrite <- StageSetProperties.ub_le_1 ; auto ~ |] ;
    rewrite StageSetProperties.ub_le_2 with (m:=S (S m)) ; auto ~.
  Qed.
  
  Lemma eq_ssubst_3_fill_ge_2_strong:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) (dg_ebox dg) (dg::dgs) in
    match cs with
    | c1 :: c1' :: cs => 
      match c1 with
      | nil => False
      | _ => forall (m:nat), 
        S (length cs) <= m < length bs ->
        let b := hd 0 bs in
        eq_context_ssubst_3 m h (length c1') v b 0 c1 c1 ->
        forall (ss:StageSet.t),
        StageSet.ub m ss = true ->
        (M.ssubst (S m) (match (S m) with
	  | S (S m) => if ltb h (0 + (length c1)) && leb 0 h
       		then StageSet.add (S m) (match m with
                  | 0 => ss
                  | S m0 =>
                      if ltb h (b + length c1') && leb b h
                      then StageSet.add (S m0) ss
                      else ss
                  end) else (match m with
                  | 0 => ss
                  | S m0 =>
                      if ltb h (b + length c1') && leb b h
                      then StageSet.add (S m0) ss
                      else ss
                  end)
	  | _ => ss
          end) (M.cast_var (hole_var h)) e0 v) = e0 ->


        (M.ssubst m (match m with
	  | S (S m) => if ltb h (b + (length c1')) && leb b h
       		then StageSet.add (S m) ss else ss
	  | _ => ss
          end) (M.cast_var (hole_var h)) 
          (Context.fill dg c1 (ret dg (cast_ebox dg e0))) v) = 
          (Context.fill dg c1 (ret dg (cast_ebox dg e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (context_stack_not_nil e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros CSNotNil.
    destruct (trans e (0::bs) (dg_ebox dg) (dg::dgs)).
    destruct t ; auto ~.
    destruct t0 ; auto ~.
    destruct t ; auto ~.
    exfalso ; apply CSNotNil ; simpl ; auto ~.
    simpl ; rewrite andb_true_r in *|-* ; intros.

    simpl in *|-*.
    
    inversion H0.
    subst c1 u2 c2 p.
    clear H0 CSNotNil.
    destruct bs ; [exfalso ; generalize H ; clear ; simpl ; intros ; omega|].
    simpl in *|-*.
    generalize dependent u1 ; generalize dependent ss.
    induction t ; simpl ; unfold eq_ssubst_3 ; intros.

    destruct m ; [exfalso ; omega|].
    rewrite MP.ssubst_bind with (f2:=
    (fun v0 : T.expr =>
      cast_eapp dg (cast_eabs dg (cast_var (hole_var 0)) (ret dg (cast_ebox dg e0))) v0)).
    rewrite H6 ; auto ~.
    intros.
    rewrite MP.ssubst_eapp, MP.ssubst_eabs, MP.ssubst_ret, MP.ssubst_ebox.
    simpl in *|-*.

    assert(beq_var (hole_var h) (hole_var 0) = ltb h 1) as Eq1.
    clear ; simpl ; remember (ltb h 1) ; destruct b ; symmetry in Heqb.
    apply beq_nat_true_iff ; apply leb_iff in Heqb ; unfold hole_var ; omega.
    apply beq_nat_false_iff ; apply leb_iff_conv in Heqb ; unfold hole_var ; omega.
    destruct m ; destruct (ltb h (n + (length t0)) && leb n h) ; rewrite Eq1, H2 ; auto ~.

    inversion H8 ; clear H8.
    subst c1 u2 c2 a.
    destruct m ; [exfalso ; omega|].

    rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr =>
     cast_eapp dg
     (cast_eabs dg (cast_var (hole_var (S (length t))))
        (bind dg u0
           (fun v1 : T.expr =>
            cast_eapp dg
              (cast_eabs dg (cast_var (hole_var (length t)))
                 (Context.fill dg t (ret dg (cast_ebox dg e0)))) v1))) v0)).
    rewrite H6 ; auto ~.
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
      destruct m ; [| destruct (ltb (S (length t)) (n + (length t0)) && leb n (S (length t))) ] ;
      try(rewrite StageSetProperties.add_add) ; rewrite IHt ; auto ~ ;
      try(rewrite StageSetProperties.add_mem_4 ; auto ~) ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto ~).
      rewrite StageSetProperties.add_add ; auto ~.

      (* Case h < S length t *)
      assert(beq_var (hole_var h) (hole_var (S (length t))) = false) as False1.
      apply beq_nat_false_iff ; unfold hole_var ; omega.
      rewrite False1, IHt ; auto ~.
      assert(ltb h (S (length t)) = ltb h (S (S (length t)))) as Eq1.
      remember (ltb h (S (S (length t)))) ; destruct b ; symmetry in Heqb.
      apply leb_iff ; apply leb_iff in Heqb ; omega.
      apply leb_iff_conv ; apply leb_iff_conv in Heqb ; omega.
      rewrite Eq1 ; auto ~.
  Qed.

  Lemma eq_ssubst_3_fill_gt_2:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) (dg_ebox dg) (dg::dgs) in
    match cs with
    | c1 :: c1' :: cs => 
      match c1 with
      | nil => False
      | _ => forall (m:nat), 
        S (length cs) < m < length bs ->
        let b := hd 0 bs in
        eq_ssubst_3 (S m) h (length c1) v 0 e0 e0 ->
        eq_context_ssubst_3 m h (length c1') v b 0 c1 c1 ->
        eq_ssubst_3 m h (length c1') v b
        (Context.fill dg c1 (ret dg (cast_ebox dg e0))) 
        (Context.fill dg c1 (ret dg (cast_ebox dg e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (eq_ssubst_3_fill_ge_2_strong e bs dg dgs) ; intros Strong1.
    destruct (trans e (0::bs) (dg_ebox dg) (dg::dgs)).
    destruct t ; auto ~.
    destruct t0 ; auto ~.
    destruct t ; auto ~.
    unfold eq_ssubst_3 ; intros.
    apply Strong1 ; auto ~.
    simpl plus in *|-* ; simpl length in *|-*.
    omega.
    destruct m.
    apply H0 ; auto ~.
    rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto ~.
    destruct m.
    apply H0 ; auto ~.
    rewrite StageSetProperties.ub_le_2 with (m:=1) ; auto ~.
    apply H0 ; auto ~.
    destruct (ltb h (hd 0 bs + (length t0)) && leb (hd 0 bs) h) ; [
    rewrite <- StageSetProperties.ub_le_1 ; auto ~ |] ;
    rewrite StageSetProperties.ub_le_2 with (m:=S (S m)) ; auto ~.
  Qed.

  Lemma eq_ssubst_3_sum:
    forall (e v:T.expr) (n m1 m2 b1 b2:nat) (h:S.var),
    eq_ssubst_3 n h m1 v b1 e e ->
    (b1 + m1 = b2 + m2)%nat ->
    b2 <= b1 ->
    eq_ssubst_3 n h m2 v b2 e e.
  Proof.
    unfold eq_ssubst_3 ; intros.
    destruct n ; try(apply H ; auto ~ ; fail).
    destruct n ; try(apply H ; auto ~ ; fail).
    remember (ltb h (b1 + m1) && leb b1 h) ; destruct b ; symmetry in Heqb.
    assert(ltb h (b2 + m2) && leb b2 h = true) as True1.
    apply andb_true_iff in Heqb ; destruct Heqb.
    apply andb_true_iff ; split ; apply leb_iff ;
    apply leb_iff in H3 ; apply leb_iff in H4 ; omega.
    rewrite True1 ; apply H ; auto ~.
    apply H ; auto ~.
    destruct (ltb h (b2 + m2) && leb b2 h) ; auto ~.
    rewrite <- StageSetProperties.ub_le_1 ; auto ~.
  Qed.

  Lemma eq_context_ssubst_3_sum:
    forall (c:Context.t) (v:T.expr) (n m1 m2 b1 b2 b3:nat) (h:S.var),
    eq_context_ssubst_3 n h m1 v b1 b3 c c ->
    (b1 + m1 = b2 + m2)%nat ->
    b2 <= b1 ->
    eq_context_ssubst_3 n h m2 v b2 b3 c c.
  Proof.
    induction c ; simpl ; intros.
    constructor.
    inversion H ; subst.
    constructor ; auto ~.
    apply eq_ssubst_3_sum with (m1:=m1) (b1:=b1) ; auto ~.
    apply IHc with (m1:=m1) (b1:=b1) ; auto ~.
  Qed.

  Lemma eq_ssubst_3_merge:
    forall (e1 e2:S.expr) (bs:list nat) (dg1 dg2:dg_t) (dgs1 dgs2:list dg_t) (h:S.var) (v:T.expr),
    let (e1', cs1) := trans e1 (map_iter_booker e2 bs 0) dg1 dgs1 in
    let (e2', cs2) := trans e2 bs dg2 dgs2 in
    forall (m:nat),
    max (depth e1) (depth e2) <= m < length bs ->
    eq_stack_ssubst_3 (pred m) h v (tl (map_iter_booker e2 bs 0))
       (hd 0 (map_iter_booker e2 bs 0)) cs1 cs1 ->
    eq_stack_ssubst_3 (pred m) h v (tl bs) (hd 0 bs) cs2 cs2 ->
    eq_stack_ssubst_3 (pred m) h v (tl bs) (hd 0 bs) (Context.merge cs1 cs2)
      (Context.merge cs1 cs2).
  Proof.
    intros.
    specialize (map_iter_booker_stack e2 bs dg2 dgs2) ; intros MapIterBooker2.
    specialize (depth_length e1 (map_iter_booker e2 bs 0) dg1 dgs1) ; intros DpthLength1.
    specialize (depth_length e2 bs dg2 dgs2) ; intros DpthLength2.
    destruct (trans e1) ; destruct (trans e2) ; intros.
    rewrite DpthLength1, DpthLength2 in H ; clear DpthLength1 DpthLength2.
    rewrite MapIterBooker2 in H0 ; clear MapIterBooker2.
    
    generalize dependent m ; generalize dependent t ;
    generalize dependent bs.
    induction t0 ; simpl ; intros ; auto ~.
    rewrite ContextStaticProperties.merge_nil_r ; simpl ; auto ~.
    destruct bs ; [exfalso ; simpl in *|-* ; omega|].

    assert(forall (bs:list nat) (m:nat), bs = 
      (tl (map_iter_stack nil (n :: bs) m))) as Eq1.
    induction bs0 ; simpl in *|-* ; intros ; auto ~.
    rewrite <- IHbs0 ; auto ~.
    rewrite plus_0_r ; simpl ; auto ~.

    rewrite <- Eq1 in H0.
    simpl in *|-* ; rewrite plus_0_r in H0 ; auto ~.

    destruct bs ; [exfalso ; simpl in *|-* ; omega|].
    destruct t ; [simpl in *|-* |] ; auto ~.
    destruct m ; [simpl in *|-* ; exfalso ; omega|].
    destruct bs ; [exfalso ; simpl in *|-* ; omega|].

    specialize (IHt0 (n0::bs) t1).
    simpl in IHt0.
    assert(eq_stack_ssubst_3 (pred m) h v bs n0 (Context.merge t1 t0)
         (Context.merge t1 t0)) as IH.
    apply IHt0 ; auto ~.
    simpl in H ; omega.

    
    assert(forall (bs:list nat) (n0 m:nat), 
      map_iter_stack t0 (n0 :: bs) m = 
      tl (map_iter_stack (a :: t0) (n :: n0 :: bs) m)) as Eq2.
    induction bs0 ; simpl in *|-* ; intros ; auto ~.
    unfold map_iter_stack in *|-* ; simpl.
    specialize (IHbs0 a0 (S m0)).
    simpl in IHbs0.
    rewrite IHbs0 ; auto ~.
    rewrite <- Eq2 in H0.
    inversion H0 ; subst ; auto ~.
    constructor.

    simpl in *|-*.
    inversion H1 ; subst ; auto ~.
    constructor.
    clear IHt0.

    simpl in *|-*.

    inversion H0 ; subst ; [simpl in *|-*|].
    inversion H1 ; subst ; simpl in *|-*.
    constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    rewrite plus_0_r in H5 ; auto ~.

    constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    apply eq_context_ssubst_3_sum with (m1:=0) (b1:=(n0 + length c1')%nat) ; auto ~ ; omega.

    inversion H1 ; subst.
    simpl ; constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; simpl in *|-* ; auto ~.
    simpl in *|-* ; rewrite plus_0_r in H6 ; auto ~.
    apply eq_context_ssubst_3_m_ge with (m:=0) ; auto ~ ; omega.

    constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.

    simpl in *|-* ; auto ~.
    apply eq_context_ssubst_3_sum with (m1:=length c1') (b1:=(n0 + length c1'0)%nat) ; auto ~ ; try(omega).
    rewrite app_length ; omega.

    apply eq_context_ssubst_3_m_ge with (m:=length c1'0) ; auto ~.
    rewrite app_length ; omega.
  Qed.

  Lemma eq_ssubst_3_gt:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t) (h:S.var) (v:T.expr),
    let n := depth e in
    let (e0, cs) := trans e bs dg dgs in
    forall (m:nat), 
    n < m < length bs ->
    eq_ssubst_3 m h (booker e 0) v (nth 0 bs 0) e0 e0 /\
    eq_stack_ssubst_3 (pred m) h v 
                       (List.tl bs) (List.hd 0 bs) cs cs /\
    (svalue 0 e -> eq_ssubst_3 m h (booker e 0) v (nth 0 bs 0) 
    (phi e bs dg dgs) (phi e bs dg dgs)).
  Proof.
    assert(forall (h v:nat), beq_nat (hole_var h) (source_var v) = false) as BeqFalse.
      intros ; apply beq_nat_false_iff ; unfold hole_var, source_var ; omega.

    induction e ; simpl ; intros.

    (* EConst *)
    unfold eq_ssubst_3 ; repeat(split) ; intros ;
    [rewrite MP.ssubst_ret | constructor |] ; 
    rewrite MP.ssubst_econst ; auto ~.

    
    (* EVar *)
    unfold eq_ssubst_3 ; repeat(split) ; intros ;
    [rewrite MP.ssubst_ret | constructor |] ;
    rewrite MP.ssubst_evar, BeqFalse ; auto ~.

    (* EAbs *)
    specialize (IHe bs (dg_eabs dg v) dgs h v0) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_3 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ~ ; [
    rewrite MP.ssubst_ret, MP.ssubst_eabs, BeqFalse, H1 |
    destruct H1 | rewrite MP.ssubst_eabs, BeqFalse, H2 ] ; auto ~.

    (* EFix *)
    specialize (IHe bs (dg_efix dg v v0) dgs h v1) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_3 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ~ ; [
    rewrite MP.ssubst_ret, MP.ssubst_efix, BeqFalse, BeqFalse ; simpl ; rewrite H1 |
    destruct H1 | rewrite MP.ssubst_efix, BeqFalse, BeqFalse ; simpl ; rewrite H2 ] ; auto ~.
    
    (* EApp *)
    specialize (eq_ssubst_3_merge e1 e2 bs (dg_eapp_l dg) (dg_eapp_r dg) dgs dgs h v) ; intros EqMerge.
    specialize (IHe1 (map_iter_booker e2 bs 0) (dg_eapp_l dg) dgs h v) ;
    specialize (IHe2 bs (dg_eapp_r dg) dgs h v) ;
    destruct (trans e1) ; destruct (trans e2) ; intros.
    unfold eq_ssubst_3 ; repeat(split) ; intros.

    assert(ltb h (nth 0 (map_iter_booker e2 bs 0) 0 + booker e1 0) &&
           leb (nth 0 (map_iter_booker e2 bs 0) 0) h = true ->
    ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) &&
         leb (nth 0 bs 0) h = true) as Eq1.
      generalize H ; clear ; intros BS ; intros ; apply andb_true_iff in H ; destruct H.
      apply leb_iff in H ; apply leb_iff in H0.
      rewrite StaticProperties.map_iter_booker_nth_indep in H, H0 ; auto ~ ; try(omega).
      apply andb_true_iff ; split ; apply leb_iff ; simpl in *|-*; try(omega).
     remember (CRaw.svalueb 0 e1) ; destruct b ; symmetry in Heqb.
    
      (* Case svalue 0 e1 *)
      destruct H ; apply Nat.max_lub_lt_iff in H ; auto ~ ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto ~.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto ~.
      rewrite MP.ssubst_bind with (f2:=(fun v2 : T.expr => 
        cast_eapp dg (phi e1 (map_iter_booker e2 bs 0) (dg_eapp_l dg) dgs) v2)).
      destruct m ; [rewrite H5 ; auto ~|].
      destruct m ; [rewrite H5 ; auto ~|].
      unfold eq_ssubst_3 in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0) && leb (nth 0 bs 0) h) ; 
      destruct b ; symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) &&
         leb (nth 0 bs 0) h = true) as LtbTrue.
      apply andb_true_iff ; apply andb_true_iff in Heqb0 ; destruct Heqb0.
      apply leb_iff in H7 ; apply leb_iff in H8.
      split ; apply leb_iff ; omega.
      rewrite LtbTrue, H5 ; auto ~.
      rewrite H5 ; auto ~.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) && leb (nth 0 bs 0) h) ; auto ~.
      rewrite <- StageSetProperties.ub_le_1 ; auto ~.
      intros ; rewrite MP.ssubst_eapp ; destruct H4.
      apply CalculusProperties.svalueb_iff in Heqb.
      destruct m ; [rewrite H7 ; auto ~|].
      destruct m ; [rewrite H7 ; auto ~|].
      unfold eq_ssubst_3 in H7.
      remember (ltb h (nth 0 (map_iter_booker e2 bs 0) 0 + booker e1 0) &&
           leb (nth 0 (map_iter_booker e2 bs 0) 0) h) ;
      destruct b ; symmetry in Heqb0.
      rewrite Eq1, H7 ; auto ~.
      rewrite H7 ; auto ~.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) && leb (nth 0 bs 0) h) ; auto ~.
      rewrite <- StageSetProperties.ub_le_1 ; auto ~.

      (* Case not svalue 0 e1 *)
      destruct H ; apply Nat.max_lub_lt_iff in H ; auto ~ ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto ~.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto ~.

      rewrite MP.ssubst_bind with (f2:=(fun v1 : T.expr => 
        bind dg e0 (fun v2 : T.expr => cast_eapp dg v1 v2))).
      destruct m ; [rewrite H3 ; auto ~|].
      destruct m ; [rewrite H3 ; auto ~|].
      unfold eq_ssubst_3 in H3.
      remember (ltb h (nth 0 (map_iter_booker e2 bs 0) 0 + booker e1 0) &&
           leb (nth 0 (map_iter_booker e2 bs 0) 0) h) ; destruct b ; symmetry in Heqb0.
      rewrite Eq1, H3 ; auto ~.
      rewrite H3 ; auto ~.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) && leb (nth 0 bs 0) h) ; auto ~.
      rewrite <- StageSetProperties.ub_le_1 ; auto ~.
      intros.
      rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr => 
        cast_eapp dg (ssubst m
        match m with
        | 0 => ss
        | 1 => ss
        | S (S n) =>
            if ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) && leb (nth 0 bs 0) h
            then StageSet.add (S n) ss
            else ss
        end (cast_var (hole_var h)) v2 v) v0)).
      destruct m ; [rewrite H5 ; auto ~ |].
      destruct m ; [rewrite H5 ; auto ~ |].
      unfold eq_ssubst_3 in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0) && leb (nth 0 bs 0) h) ;
      destruct b ; symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) &&
         leb (nth 0 bs 0) h = true) as LtbTrue.
      apply andb_true_iff in Heqb0 ; destruct Heqb0.
      apply leb_iff in H7 ; apply leb_iff in H8.
      apply andb_true_iff ; split ; apply leb_iff ; omega.
      rewrite LtbTrue, H5 ; auto ~.
      rewrite H5 ; auto ~.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) && leb (nth 0 bs 0) h) ; auto ~.
      rewrite <- StageSetProperties.ub_le_1 ; auto ~.
      intros ; rewrite MP.ssubst_eapp ; auto ~.

      destruct H ; apply Nat.max_lub_lt_iff in H ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto ~.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto ~.
      destruct H5 ; destruct H3 ; clear H2 H4 H6 H7 IHe1 IHe2.
      apply EqMerge ; auto ~.
      split ; auto ~.
      apply Nat.max_lub_iff ; omega.
      inversion H0.

    (* ELoc *)
    unfold eq_ssubst_3 ; repeat(split) ; intros ;
    [rewrite MP.ssubst_ret | constructor |] ; 
    rewrite MP.ssubst_eloc ; auto ~.

    (* ERef *)
    specialize (IHe bs (dg_eref dg) dgs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_3 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ~.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_eref dg v0)) ; 
    intros.
    rewrite H1 ; auto ~.
    rewrite MP.ssubst_eref ; reflexivity.
    destruct H1 ; auto ~.
    inversion H0.

    (* EDeref *)
    specialize (IHe bs (dg_ederef dg) dgs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_3 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ~.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_ederef dg v0)) ; 
    intros.
    rewrite H1 ; auto ~.
    rewrite MP.ssubst_ederef ; reflexivity.
    destruct H1 ; auto ~.
    inversion H0.

    (* EAssign *)
    specialize (eq_ssubst_3_merge e1 e2 bs (dg_eassign_l dg) (dg_eassign_r dg) dgs dgs h v) ; intros EqMerge.
    specialize (IHe1 (map_iter_booker e2 bs 0) (dg_eassign_l dg) dgs h v) ;
    specialize (IHe2 bs (dg_eassign_r dg) dgs h v) ;
    destruct (trans e1) ; destruct (trans e2) ; intros.
    unfold eq_ssubst_3 ; repeat(split) ; intros.

    assert(ltb h (nth 0 (map_iter_booker e2 bs 0) 0 + booker e1 0) &&
           leb (nth 0 (map_iter_booker e2 bs 0) 0) h = true ->
    ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) &&
         leb (nth 0 bs 0) h = true) as Eq1.
      generalize H ; clear ; intros BS ; intros ; apply andb_true_iff in H ; destruct H.
      apply leb_iff in H ; apply leb_iff in H0.
      rewrite StaticProperties.map_iter_booker_nth_indep in H, H0 ; auto ~ ; try(omega).
      apply andb_true_iff ; split ; apply leb_iff ; simpl in *|-*; try(omega).
     remember (CRaw.svalueb 0 e1) ; destruct b ; symmetry in Heqb.
    
      (* Case svalue 0 e1 *)
      destruct H ; apply Nat.max_lub_lt_iff in H ; auto ~ ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto ~.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto ~.
      rewrite MP.ssubst_bind with (f2:=(fun v2 : T.expr => 
        cast_eassign dg (phi e1 (map_iter_booker e2 bs 0) (dg_eassign_l dg) dgs) v2)).
      destruct m ; [rewrite H5 ; auto ~|].
      destruct m ; [rewrite H5 ; auto ~|].
      unfold eq_ssubst_3 in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0) && leb (nth 0 bs 0) h) ; 
      destruct b ; symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) &&
         leb (nth 0 bs 0) h = true) as LtbTrue.
      apply andb_true_iff ; apply andb_true_iff in Heqb0 ; destruct Heqb0.
      apply leb_iff in H7 ; apply leb_iff in H8.
      split ; apply leb_iff ; omega.
      rewrite LtbTrue, H5 ; auto ~.
      rewrite H5 ; auto ~.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) && leb (nth 0 bs 0) h) ; auto ~.
      rewrite <- StageSetProperties.ub_le_1 ; auto ~.
      intros ; rewrite MP.ssubst_eassign ; destruct H4.
      apply CalculusProperties.svalueb_iff in Heqb.
      destruct m ; [rewrite H7 ; auto ~|].
      destruct m ; [rewrite H7 ; auto ~|].
      unfold eq_ssubst_3 in H7.
      remember (ltb h (nth 0 (map_iter_booker e2 bs 0) 0 + booker e1 0) &&
           leb (nth 0 (map_iter_booker e2 bs 0) 0) h) ;
      destruct b ; symmetry in Heqb0.
      rewrite Eq1, H7 ; auto ~.
      rewrite H7 ; auto ~.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) && leb (nth 0 bs 0) h) ; auto ~.
      rewrite <- StageSetProperties.ub_le_1 ; auto ~.

      (* Case not svalue 0 e1 *)
      destruct H ; apply Nat.max_lub_lt_iff in H ; auto ~ ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto ~.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto ~.

      rewrite MP.ssubst_bind with (f2:=(fun v1 : T.expr => 
        bind dg e0 (fun v2 : T.expr => cast_eassign dg v1 v2))).
      destruct m ; [rewrite H3 ; auto ~|].
      destruct m ; [rewrite H3 ; auto ~|].
      unfold eq_ssubst_3 in H3.
      remember (ltb h (nth 0 (map_iter_booker e2 bs 0) 0 + booker e1 0) &&
           leb (nth 0 (map_iter_booker e2 bs 0) 0) h) ; destruct b ; symmetry in Heqb0.
      rewrite Eq1, H3 ; auto ~.
      rewrite H3 ; auto ~.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) && leb (nth 0 bs 0) h) ; auto ~.
      rewrite <- StageSetProperties.ub_le_1 ; auto ~.
      intros.
      rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr => 
        cast_eassign dg (ssubst m
        match m with
        | 0 => ss
        | 1 => ss
        | S (S n) =>
            if ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) && leb (nth 0 bs 0) h
            then StageSet.add (S n) ss
            else ss
        end (cast_var (hole_var h)) v2 v) v0)).
      destruct m ; [rewrite H5 ; auto ~ |].
      destruct m ; [rewrite H5 ; auto ~ |].
      unfold eq_ssubst_3 in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0) && leb (nth 0 bs 0) h) ;
      destruct b ; symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) &&
         leb (nth 0 bs 0) h = true) as LtbTrue.
      apply andb_true_iff in Heqb0 ; destruct Heqb0.
      apply leb_iff in H7 ; apply leb_iff in H8.
      apply andb_true_iff ; split ; apply leb_iff ; omega.
      rewrite LtbTrue, H5 ; auto ~.
      rewrite H5 ; auto ~.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) && leb (nth 0 bs 0) h) ; auto ~.
      rewrite <- StageSetProperties.ub_le_1 ; auto ~.
      intros ; rewrite MP.ssubst_eassign ; auto ~.

      destruct H ; apply Nat.max_lub_lt_iff in H ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto ~.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto ~.
      destruct H5 ; destruct H3 ; clear H2 H4 H6 H7 IHe1 IHe2.
      apply EqMerge ; auto ~.
      split ; auto ~.
      apply Nat.max_lub_iff ; omega.
      inversion H0.

    (* EBox *)
    specialize (IHe (0::bs) (dg_ebox dg) (dg::dgs) h v) ;
    specialize (booker_length e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros BKLength.
    specialize (depth_length e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros DpthLength1.
    specialize (eq_ssubst_3_fill_gt_1 e bs dg dgs) ; intros EqFill1.
    specialize (eq_ssubst_3_fill_gt_2 e bs dg dgs) ; intros EqFill2.
    destruct (trans e) ; intros.
    destruct t ; simpl in *|-* ; intros.

      (* depth e = 0 *)
      unfold eq_ssubst_3 ; repeat(split) ; intros.

      rewrite MP.ssubst_ret, MP.ssubst_ebox ;
      rewrite DpthLength1 in *|-* ;
      rewrite BKLength in *|-* ; simpl in *|-* ;
      destruct IHe with (m:=S m) ; auto ~ ; try(omega).
      unfold eq_ssubst_3 in H1 ; simpl in H1 ;
      destruct m ; rewrite H1 ; auto ~ ; [
      rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto ~ | ] ;
      destruct m ; auto ~ ; destruct (ltb h (nth 0 bs 0 + 0) && leb (nth 0 bs 0) h) ; auto ~ ;
      try(rewrite StageSetProperties.ub_le_2 with (m:=1) ; auto ~ ; omega) ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto ~) ;
      try(apply StageSetProperties.ub_le_2 with (m:=(S (S m))) ; auto ~).

      constructor.

      rewrite MP.ssubst_ebox ;
      rewrite DpthLength1 in *|-* ;
      rewrite BKLength in *|-* ; simpl in *|-* ;
      destruct IHe with (m:=S m) ; auto ~ ; try(omega) ;
      unfold eq_ssubst_3 in H2 ; simpl in H2 ;
      destruct m ; rewrite H2 ; auto ~ ; [
      rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto ~ | ] ;
      destruct m ; auto ~ ; destruct (ltb h (nth 0 bs 0 + 0) && leb (nth 0 bs 0) h) ; auto ~ ;
      try(rewrite StageSetProperties.ub_le_2 with (m:=1) ; auto ~ ; omega) ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto ~) ;
      try(apply StageSetProperties.ub_le_2 with (m:=(S (S m))) ; auto ~).

      (* depth e > 0 *)
      rewrite DpthLength1 in H.
      destruct IHe with (m:=S m) ; auto ~ ; try(omega).
      repeat(split) ; intros ; simpl in *|-*.
      destruct H1 ; clear H2 IHe.
      rewrite BKLength ; rewrite BKLength in H0.
      inversion H1 ; subst ; simpl in *|-*.
      
      specialize (EqFill1 h v).
      destruct t ; [contradiction|].
      apply EqFill1 ; auto ~.

      specialize (EqFill2 h v).
      destruct t ; [contradiction|].
      apply EqFill2 ; auto ~.
      
      destruct H1 ; inversion H1 ; subst ; auto ~ ; constructor.
      inversion H2 ; subst.
      apply CalculusProperties.depth_svalue in H5 ; exfalso ; omega.
    
    (* EUnbox *)
    destruct bs ; simpl in *|-*.
    destruct (List2.hd_cons dgs dg_empty).
    specialize (IHe nil d l h v) ; destruct (trans e).
    intros ; destruct m ; exfalso ; omega.

    destruct (List2.hd_cons dgs dg_empty).
    specialize (IHe bs d l h v).
    specialize (context_stack_not_nil e bs d l) ; intros CSNotNil.
    specialize (depth_length e bs d l) ; intros DpthLength.
    specialize (booker_length e bs d l) ; intros BKLength.
    destruct (trans e) ; intros.
    destruct m ; [exfalso ; omega| simpl in *|-*].

    unfold eq_ssubst_3 ; repeat(split) ; intros ; simpl in *|-*.
    rewrite MP.ssubst_eunbox, MP.ssubst_evar.
    destruct m ; auto ~ ; simpl in *|-*.
    assert(beq_nat (hole_var h) (hole_var n) = false) as BeqFalse1.
    apply beq_nat_false_iff ; unfold hole_var ; omega.
    rewrite BeqFalse1 ; simpl ; constructor.

    remember (ltb h (n + 1) && leb n h).
    destruct b ; symmetry in Heqb ; unfold ltb in Heqb.
    assert(CRaw.BindingSet.rho (S m)
           (StageSet.remove (S (S m)) (StageSet.add (S m) ss)) = false) as RhoFalse.
    rewrite BindingSetProperties.rho_false_mem ; auto ~.
    rewrite StageSetProperties.remove_mem_1 ; auto ~.
    apply StageSetProperties.add_mem_3 ; auto ~.
    rewrite RhoFalse ; simpl ; rewrite andb_false_r ; constructor.
    assert(beq_nat (hole_var h) (hole_var n) = false) as BeqFalse1.
    apply andb_false_iff in Heqb ; destruct Heqb ;
    apply leb_iff_conv in H1 ; apply beq_nat_false_iff ;
    unfold hole_var ; omega.
    rewrite BeqFalse1 ; simpl ; constructor. 

    destruct IHe with (m:=m) ; auto ~ ; try(omega).
    destruct bs ; simpl in *|-*.
    exfalso ; omega.
    destruct t ; simpl.
    assert((e0, n) = (e0, (n+length(tl ((e0, n) :: nil)))%nat)) as Eq1.
    rewrite plus_0_r ; auto ~.
    simpl tl in Eq1.
    rewrite Eq1 ; clear Eq1.
    constructor ; auto ~.
    rewrite BKLength in H0 ; simpl in H0.
    repeat(constructor ; auto ~).
    constructor ; auto ~.
    assert((e0, n) = (e0, (n+length(tl ((e0, n) :: nil)))%nat)) as Eq1.
    rewrite plus_0_r ; auto ~.
    simpl tl in Eq1.
    rewrite Eq1 ; clear Eq1.
    constructor ; auto ~.
    rewrite BKLength in H0 ; simpl in H0 ; auto ~.
    constructor.
    destruct H1 ; auto ~.
    inversion H0.

    (* ERun *)
    specialize (IHe bs (dg_erun dg) dgs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_3 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ~.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_erun dg v0)) ; 
    intros.
    rewrite H1 ; auto ~.
    rewrite MP.ssubst_erun ; reflexivity.
    destruct H1 ; auto ~.
    inversion H0.

    (* ELift *)
    specialize (IHe bs (dg_elift dg) dgs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_3 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ~.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_elift dg v0)) ; 
    intros.
    rewrite H1 ; auto ~.
    rewrite MP.ssubst_elift ; reflexivity.
    destruct H1 ; auto ~.
    inversion H0.
  Qed.

End EqSubstProperties3.

Module EqSubstProperties2 (R:Replacement) (S:ReplacementCalculus R)
    (T:StagedCalculus) (DG:DataGathering R S) 
    (DGP:DataGatheringPredicates R S DG)
    (DGR:DataGatheringRequirements R S DG DGP)
    (M:Monad R S T DG) (MP:MonadStepProperties R S T DG DGP DGR M)
    (TrSP:TranslationStaticProperties R S T DG DGP DGR M MP.Translation).

  Module Translation := MP.Translation.
  Module StaticProperties := TrSP.
  Module ContextStaticProperties := TrSP.ContextStaticProperties.
  Module CalculusProperties := CalculusProperties R S.
  Module BindingSetProperties := BindingSetProperties R S.CRaw.BindingSet.
  Import StaticProperties.
  Import Translation.
  Import S.
  Import M.
  Import DG.

  Definition eq_ssubst_2 (n:nat) (h:CRaw.var) 
      (m:nat) (v:T.expr) (b:nat) (u1 u2:T.expr) : Prop :=
      forall (ss:StageSet.t),
      StageSet.ub n ss = true ->
      (M.ssubst n (match n with
	  | S n => if ltb h (b + m) 
       		then StageSet.add n ss else ss
	  | _ => ss
          end) (M.cast_var (hole_var h)) u1 v) = u2.

  Definition eq_context_ssubst_2 := ContextStaticProperties.congr_context_ssubst eq_ssubst_2.
  Definition eq_stack_ssubst_2 := ContextStaticProperties.congr_stack_ssubst eq_ssubst_2.

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
    apply H ; auto ~.
    apply H ; auto ~.
    rewrite <- StageSetProperties.ub_le_1 ; auto ~.
    destruct n.
    apply H ; auto ~.
    assert(ltb h (b + S m) = ltb h (b + m)) as Eq1.
    generalize E ; clear ; intros.
    remember (ltb h (b + m)) ; destruct b0 ; symmetry in Heqb0 ;
    [apply leb_iff ; apply leb_iff in Heqb0 | 
    apply leb_iff_conv ; apply leb_iff_conv in Heqb0] ; omega.
    rewrite Eq1 ; apply H ; auto ~.
  Qed.

  Lemma eq_ssubst_2_m_ge:
    forall (e:T.expr) (b:nat) (h:S.var) (v:T.expr) (n m p:nat),
    eq_ssubst_2 n h m v b e e -> 
    m <= p -> eq_ssubst_2 n h p v b e e.
  Proof.
    intros.
    induction H0 ; auto ~.
    apply eq_ssubst_2_m_Sm ; auto ~.
  Qed.

  Lemma eq_context_ssubst_2_m_ge:
    forall (c:Context.t) (b1 b2:nat) (h:S.var) (v:T.expr) (n m p:nat),
    eq_context_ssubst_2 n h m v b1 b2 c c -> 
    m <= p -> eq_context_ssubst_2 n h p v b1 b2 c c.
  Proof.
    intros.
    induction c ; auto ~.
    constructor.
    inversion H ; subst.
    constructor ; auto ~.
    apply eq_ssubst_2_m_ge with (m:=m) ; auto ~.
    apply IHc ; auto ~.
  Qed.

  Lemma eq_ssubst_2_fill_ge_1_strong:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) (dg_ebox dg) (dg::dgs) in
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
          end) (M.cast_var (hole_var h)) 
          (Context.fill dg c1 (ret dg (cast_ebox dg e0))) v) = 
          (Context.fill dg c1 (ret dg (cast_ebox dg e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (context_stack_not_nil e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros CSNotNil.
    destruct (trans e (0::bs)).
    destruct t ; auto ~.
    destruct t0 ; auto ~.
    destruct t ; auto ~.
    exfalso ; apply CSNotNil ; simpl ; auto ~.
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
      cast_eapp dg (cast_eabs dg (cast_var (hole_var 0)) 
      (ret dg (cast_ebox dg e0))) v0)).
    rewrite H6 ; auto ~.
    intros.
    rewrite MP.ssubst_eapp, MP.ssubst_eabs, MP.ssubst_ret, MP.ssubst_ebox.
    simpl in *|-*.

    assert(beq_var (hole_var h) (hole_var 0) = ltb h 1) as Eq1.
    clear ; simpl ; remember (ltb h 1) ; destruct b ; symmetry in Heqb.
    apply beq_nat_true_iff ; apply leb_iff in Heqb ; unfold hole_var ; omega.
    apply beq_nat_false_iff ; apply leb_iff_conv in Heqb ; unfold hole_var ; omega.
    destruct m ; destruct (ltb h (n + 0)) ; rewrite Eq1, H2 ; auto ~.

    inversion H8 ; clear H8.
    substs.

    rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr =>
     cast_eapp dg
     (cast_eabs dg (cast_var (hole_var (S (length t))))
        (bind dg u0
           (fun v1 : T.expr =>
            cast_eapp dg
              (cast_eabs dg (cast_var (hole_var (length t)))
                 (Context.fill dg t (ret dg (cast_ebox dg e0)))) v1))) v0)).
    rewrite H6 ; auto ~.
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
      try(rewrite StageSetProperties.add_add) ; rewrite IHt ; auto ~ ;
      try(rewrite StageSetProperties.add_mem_4 ; auto ~) ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto ~).
      rewrite StageSetProperties.add_add ; auto ~.

      (* Case h < S length t *)
      assert(beq_var (hole_var h) (hole_var (S (length t))) = false) as False1.
      apply beq_nat_false_iff ; unfold hole_var ; omega.
      rewrite False1, IHt ; auto ~.
      assert(ltb h (S (length t)) = ltb h (S (S (length t)))) as Eq1.
      remember (ltb h (S (S (length t)))) ; destruct b ; symmetry in Heqb.
      apply leb_iff ; apply leb_iff in Heqb ; omega.
      apply leb_iff_conv ; apply leb_iff_conv in Heqb ; omega.
      rewrite Eq1 ; auto ~.
  Qed.

  Lemma eq_ssubst_2_fill_ge_1:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) (dg_ebox dg) (dg::dgs) in
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
        (Context.fill dg c1 (ret dg (cast_ebox dg e0))) 
        (Context.fill dg c1 (ret dg (cast_ebox dg e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (eq_ssubst_2_fill_ge_1_strong e bs dg dgs) ; intros Strong1.
    destruct (trans e (0::bs) (dg_ebox dg) (dg::dgs)).
    destruct t ; auto ~.
    destruct t0 ; auto ~.
    destruct t ; auto ~.
    unfold eq_ssubst_2 ; intros.
    apply Strong1 ; auto ~.
    simpl plus in *|-* ; simpl length in *|-*.
    destruct m.
    apply H0 ; auto ~.
    rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto ~.
    apply H0 ; auto ~.
    destruct (ltb h (hd 0 bs + 0)) ; [
    rewrite <- StageSetProperties.ub_le_1 ; auto ~ |] ;
    rewrite StageSetProperties.ub_le_2 with (m:=S m) ; auto ~.
  Qed.

  Lemma eq_ssubst_2_fill_ge_2_strong:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) (dg_ebox dg) (dg::dgs) in
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
          end) (M.cast_var (hole_var h)) 
          (Context.fill dg c1 (ret dg (cast_ebox dg e0))) v) = 
          (Context.fill dg c1 (ret dg (cast_ebox dg e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (context_stack_not_nil e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros CSNotNil.
    destruct (trans e (0::bs) (dg_ebox dg) (dg::dgs)).
    destruct t ; auto ~.
    destruct t0 ; auto ~.
    destruct t ; auto ~.
    exfalso ; apply CSNotNil ; simpl ; auto ~.
    simpl ; intros.

    simpl in *|-*.
    
    inversion H0.
    substs.
    clear H0 CSNotNil.
    destruct bs ; [exfalso ; generalize H ; clear ; simpl ; intros ; omega|].
    simpl in *|-*.
    generalize dependent u1 ; generalize dependent ss.
    induction t ; simpl ; intros.

    destruct m ; [exfalso ; omega|].
    rewrite MP.ssubst_bind with (f2:=
    (fun v0 : T.expr =>
      cast_eapp dg (cast_eabs dg (cast_var (hole_var 0)) 
      (ret dg (cast_ebox dg e0))) v0)).
    rewrite H6 ; auto ~.
    intros.
    rewrite MP.ssubst_eapp, MP.ssubst_eabs, MP.ssubst_ret, MP.ssubst_ebox.
    simpl in *|-*.

    assert(beq_var (hole_var h) (hole_var 0) = ltb h 1) as Eq1.
    clear ; simpl ; remember (ltb h 1) ; destruct b ; symmetry in Heqb.
    apply beq_nat_true_iff ; apply leb_iff in Heqb ; unfold hole_var ; omega.
    apply beq_nat_false_iff ; apply leb_iff_conv in Heqb ; unfold hole_var ; omega.
    destruct m ; destruct (ltb h (n + (length t0))) ; rewrite Eq1, H2 ; auto ~.

    inversion H8 ; clear H8.
    subst c1 u2 c2 a.
    destruct m ; [exfalso ; omega|].

    rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr =>
     cast_eapp dg
     (cast_eabs dg (cast_var (hole_var (S (length t))))
        (bind dg u0
           (fun v1 : T.expr =>
            cast_eapp dg
              (cast_eabs dg (cast_var (hole_var (length t)))
                 (Context.fill dg t (ret dg (cast_ebox dg e0)))) v1))) v0)).
    rewrite H6 ; auto ~.
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
      try(rewrite StageSetProperties.add_add) ; rewrite IHt ; auto ~ ;
      try(rewrite StageSetProperties.add_mem_4 ; auto ~) ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto ~).
      rewrite StageSetProperties.add_add ; auto ~.

      (* Case h < S length t *)
      assert(beq_var (hole_var h) (hole_var (S (length t))) = false) as False1.
      apply beq_nat_false_iff ; unfold hole_var ; omega.
      rewrite False1, IHt ; auto ~.
      assert(ltb h (S (length t)) = ltb h (S (S (length t)))) as Eq1.
      remember (ltb h (S (S (length t)))) ; destruct b ; symmetry in Heqb.
      apply leb_iff ; apply leb_iff in Heqb ; omega.
      apply leb_iff_conv ; apply leb_iff_conv in Heqb ; omega.
      rewrite Eq1 ; auto ~.
  Qed.

  Lemma eq_ssubst_2_fill_ge_2:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t) (h:S.var) (v:T.expr),
    let (e0, cs) := trans e (0::bs) (dg_ebox dg) (dg::dgs) in
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
        (Context.fill dg c1 (ret dg (cast_ebox dg e0))) 
        (Context.fill dg c1 (ret dg (cast_ebox dg e0)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (eq_ssubst_2_fill_ge_2_strong e bs dg dgs) ; intros Strong1.
    destruct (trans e (0::bs)).
    destruct t ; auto ~.
    destruct t0 ; auto ~.
    destruct t ; auto ~.
    unfold eq_ssubst_2 ; intros.
    apply Strong1 ; auto ~.
    simpl plus in *|-* ; simpl length in *|-*.
    clear Strong1.
    destruct m ; [exfalso ; omega|].
    apply H0 ; auto ~.

    destruct (ltb h (hd 0 bs + (length t0))) ; [
    rewrite <- StageSetProperties.ub_le_1 ; auto ~ |] ;
    rewrite StageSetProperties.ub_le_2 with (m:=S m) ; auto ~.
  Qed.

  Lemma eq_ssubst_2_sum:
    forall (e v:T.expr) (n m1 m2 b1 b2:nat) (h:S.var),
    eq_ssubst_2 n h m1 v b1 e e ->
    (b1 + m1 = b2 + m2)%nat ->
    eq_ssubst_2 n h m2 v b2 e e.
  Proof.
    unfold eq_ssubst_2 ; intros.
    rewrite <- H0.
    apply H ; auto ~.
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
    constructor ; auto ~.
    apply eq_ssubst_2_sum with (m1:=m1) (b1:=b1) ; auto ~.
    apply IHc with (m1:=m1) (b1:=b1) ; auto ~.
  Qed.

  Lemma eq_ssubst_2_merge:
    forall (e1 e2:S.expr) (bs:list nat) (dg1 dg2:dg_t) (dgs1 dgs2:list dg_t) (h:S.var) (v:T.expr),
    let (e1', cs1) := trans e1 (map_iter_booker e2 bs 0) dg1 dgs1 in
    let (e2', cs2) := trans e2 bs dg2 dgs2 in
    forall (m:nat),
    max (depth e1) (depth e2) <= m < length bs ->
    eq_stack_ssubst_2 (pred m) h v (tl (map_iter_booker e2 bs 0))
       (hd 0 (map_iter_booker e2 bs 0)) cs1 cs1 ->
    eq_stack_ssubst_2 (pred m) h v (tl bs) (hd 0 bs) cs2 cs2 ->
    eq_stack_ssubst_2 (pred m) h v (tl bs) (hd 0 bs) (Context.merge cs1 cs2)
      (Context.merge cs1 cs2).
  Proof.
    intros.
    specialize (map_iter_booker_stack e2 bs dg2 dgs2) ; intros MapIterBooker2.
    specialize (depth_length e1 (map_iter_booker e2 bs 0) dg1 dgs1) ; intros DpthLength1.
    specialize (depth_length e2 bs dg2 dgs2) ; intros DpthLength2.
    destruct (trans e1) ; destruct (trans e2) ; intros.
    rewrite DpthLength1, DpthLength2 in H ; clear DpthLength1 DpthLength2.
    rewrite MapIterBooker2 in H0 ; clear MapIterBooker2.
    
    generalize dependent m ; generalize dependent t ;
    generalize dependent bs.
    induction t0 ; simpl ; intros ; auto ~.
    rewrite ContextStaticProperties.merge_nil_r ; simpl ; auto ~.
    destruct bs ; [exfalso ; simpl in *|-* ; omega|].

    rewrite map_iter_stack_nil in H0 ; auto ~.

    destruct bs ; [exfalso ; simpl in *|-* ; omega|].
    destruct t ; [simpl in *|-* |] ; auto ~.
    destruct m ; [simpl in *|-* ; exfalso ; omega|].
    destruct bs ; [exfalso ; simpl in *|-* ; omega|].

    specialize (IHt0 (n0::bs) t1).
    simpl in IHt0.
    assert(eq_stack_ssubst_2 (pred m) h v bs n0 (Context.merge t1 t0)
         (Context.merge t1 t0)) as IH.
    apply IHt0 ; auto ~.
    simpl in H ; omega.

    rewrite map_iter_stack_bs, map_iter_stack_cs in H0.
    simpl in H0 ; inverts H0 ; auto ~ ; constructor.

    simpl in *|-*.
    inversion H1 ; subst ; auto ~.
    constructor.
    clear IHt0.

    simpl in *|-*.

    inversion H0 ; subst ; [simpl in *|-*|].
    inversion H1 ; subst ; simpl in *|-*.
    constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    rewrite plus_0_r in H5 ; auto ~.

    constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    apply eq_context_ssubst_2_sum with (m1:=0) (b1:=(n0 + length c1')%nat) ; auto ~.

    inversion H1 ; subst.
    simpl ; constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; simpl in *|-* ; auto ~.
    simpl in *|-* ; rewrite plus_0_r in H6 ; auto ~.
    apply eq_context_ssubst_2_m_ge with (m:=0) ; auto ~ ; omega.

    constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.

    simpl in *|-* ; auto ~.
    apply eq_context_ssubst_2_sum with (m1:=length c1') (b1:=(n0 + length c1'0)%nat) ; auto ~.
    rewrite app_length ; omega.

    apply eq_context_ssubst_2_m_ge with (m:=length c1'0) ; auto ~.
    rewrite app_length ; omega.
  Qed.

  Lemma eq_ssubst_2_ge:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t) (h:S.var) (v:T.expr),
    let n := depth e in
    let (e0, cs) := trans e bs dg dgs in
    forall (m:nat), 
    n <= m < length bs ->
    eq_ssubst_2 m h (booker e 0) v (nth 0 bs 0) e0 e0 /\
    eq_stack_ssubst_2 (pred m) h v 
                       (List.tl bs) (List.hd 0 bs) cs cs /\
    (svalue 0 e -> eq_ssubst_2 m h (booker e 0) v (nth 0 bs 0) 
      (phi e bs dg dgs) (phi e bs dg dgs)).
  Proof.
    assert(forall (h v:nat), beq_nat (hole_var h) (source_var v) = false) as BeqFalse.
      intros ; apply beq_nat_false_iff ; unfold hole_var, source_var ; omega.

    induction e ; simpl ; intros.

    (* EConst *)
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    [rewrite MP.ssubst_ret | constructor |] ; 
    rewrite MP.ssubst_econst ; auto ~.

    
    (* EVar *)
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    [rewrite MP.ssubst_ret | constructor |] ;
    rewrite MP.ssubst_evar, BeqFalse ; auto ~.

    (* EAbs *)
    specialize (IHe bs (dg_eabs dg v) dgs h v0) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ~ ; [
    rewrite MP.ssubst_ret, MP.ssubst_eabs, BeqFalse, H1 |
    destruct H1 | rewrite MP.ssubst_eabs, BeqFalse, H2 ] ; auto ~.

    (* EFix *)
    specialize (IHe bs (dg_efix dg v v0) dgs h v1) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ~ ; [
    rewrite MP.ssubst_ret, MP.ssubst_efix, BeqFalse, BeqFalse ; simpl ; rewrite H1 |
    destruct H1 | rewrite MP.ssubst_efix, BeqFalse, BeqFalse ; simpl ; rewrite H2 ] ; auto ~.
    
    (* EApp *)
    specialize (eq_ssubst_2_merge e1 e2 bs (dg_eapp_l dg) (dg_eapp_r dg) dgs dgs h v) ; intros EqMerge.
    specialize (IHe1 (map_iter_booker e2 bs 0) (dg_eapp_l dg) dgs h v) ;
    specialize (IHe2 bs (dg_eapp_r dg) dgs h v) ;
    destruct (trans e1) ; destruct (trans e2) ; intros.
    unfold eq_ssubst_2 ; repeat(split) ; intros.
    assert(nth 0 (map_iter_booker e2 bs 0) 0 + booker e1 0 =
     nth 0 bs 0 + (booker e1 0 + booker e2 0))%nat as EqNth.
     unfold map_iter_booker.
     specialize (List2Properties.map_iter_nth_indep 
      (fun b n : nat => (b + booker e2 n)%nat) bs 0 0 0) ; intros Prop1.
      rewrite Prop1 ; auto ~ ; simpl ; omega.
     remember (CRaw.svalueb 0 e1) ; destruct b ; symmetry in Heqb.
    
      (* Case svalue 0 e1 *)
      destruct H ; apply Nat.max_lub_iff in H ; auto ~ ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto ~.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto ~.
      rewrite MP.ssubst_bind with (f2:=(fun v2 : T.expr => 
        cast_eapp dg (phi e1 (map_iter_booker e2 bs 0) (dg_eapp_l dg) dgs) v2)).
      destruct m ; [rewrite H5 ; auto ~|].
      unfold eq_ssubst_2 in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0)) ; 
      destruct b ; symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))%nat = true) as LtbTrue.
      apply leb_iff ; apply leb_iff in Heqb0 ; omega.
      rewrite LtbTrue, H5 ; auto ~.
      rewrite H5 ; auto ~.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))) ; auto ~.
      rewrite <- StageSetProperties.ub_le_1 ; auto ~.
      intros ; apply CalculusProperties.svalueb_iff in Heqb.
      rewrite MP.ssubst_eapp ; destruct H4.
      destruct m ; [rewrite H7 ; auto ~|].
      unfold eq_ssubst_2 in H7.
      rewrite EqNth in H7 ; rewrite H7 ; auto ~.

      (* Case not svalue 0 e1 *)
      destruct H ; apply Nat.max_lub_iff in H ; auto ~ ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto ~.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto ~.

      rewrite MP.ssubst_bind with (f2:=(fun v1 : T.expr => 
        bind dg e0 (fun v2 : T.expr => cast_eapp dg v1 v2))).
      destruct m ; [rewrite H3 ; auto ~|].
      unfold eq_ssubst_2 in H3.
      rewrite EqNth in H3 ; rewrite H3 ; auto ~.
      intros.
      rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr => 
        cast_eapp dg (ssubst m
        match m with
        | 0 => ss
        | S n =>
            if ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))
            then StageSet.add n ss
            else ss
        end (cast_var (hole_var h)) v2 v) v0)).
      destruct m ; [rewrite H5 ; auto ~ |].
      unfold eq_ssubst_2 in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0)) ; destruct b ;
      symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) = true) as LtbTrue.
      apply leb_iff ; apply leb_iff in Heqb0 ; omega.
      rewrite LtbTrue, H5 ; auto ~.
      rewrite H5 ; auto ~.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))) ; auto ~.
      rewrite <- StageSetProperties.ub_le_1 ; auto ~.
      intros ; rewrite MP.ssubst_eapp ; auto ~.

      destruct H ; apply Nat.max_lub_iff in H ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto ~.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto ~.
      destruct H5 ; destruct H3 ; clear H2 H4 H6 H7 IHe1 IHe2.
      apply EqMerge ; auto ~.
      split ; auto ~.
      apply Nat.max_lub_iff ; omega.
      inversion H0.

    (* ELoc *)
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    [rewrite MP.ssubst_ret | constructor |] ; 
    rewrite MP.ssubst_eloc ; auto ~.

    (* ERef *)
    specialize (IHe bs (dg_eref dg) dgs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ~.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_eref dg v0)) ; 
    intros.
    rewrite H1 ; auto ~.
    rewrite MP.ssubst_eref ; reflexivity.
    destruct H1 ; auto ~.
    inversion H0.

    (* EDeref *)
    specialize (IHe bs (dg_ederef dg) dgs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ~.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_ederef dg v0)) ; 
    intros.
    rewrite H1 ; auto ~.
    rewrite MP.ssubst_ederef ; reflexivity.
    destruct H1 ; auto ~.
    inversion H0.

    (* EAssign *)
    specialize (eq_ssubst_2_merge e1 e2 bs (dg_eassign_l dg) (dg_eassign_r dg) dgs dgs h v) ; intros EqMerge.
    specialize (IHe1 (map_iter_booker e2 bs 0) (dg_eassign_l dg) dgs h v) ;
    specialize (IHe2 bs (dg_eassign_r dg) dgs h v) ;
    destruct (trans e1) ; destruct (trans e2) ; intros.
    unfold eq_ssubst_2 ; repeat(split) ; intros.
    assert(nth 0 (map_iter_booker e2 bs 0) 0 + booker e1 0 =
     nth 0 bs 0 + (booker e1 0 + booker e2 0))%nat as EqNth.
     unfold map_iter_booker.
     specialize (List2Properties.map_iter_nth_indep 
      (fun b n : nat => (b + booker e2 n)%nat) bs 0 0 0) ; intros Prop1.
      rewrite Prop1 ; auto ~ ; simpl ; omega.
     remember (CRaw.svalueb 0 e1) ; destruct b ; symmetry in Heqb.
    
      (* Case svalue 0 e1 *)
      destruct H ; apply Nat.max_lub_iff in H ; auto ~ ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto ~.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto ~.
      rewrite MP.ssubst_bind with (f2:=(fun v2 : T.expr => 
        cast_eassign dg (phi e1 (map_iter_booker e2 bs 0) (dg_eassign_l dg) dgs) v2)).
      destruct m ; [rewrite H5 ; auto ~|].
      unfold eq_ssubst_2 in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0)) ; 
      destruct b ; symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))%nat = true) as LtbTrue.
      apply leb_iff ; apply leb_iff in Heqb0 ; omega.
      rewrite LtbTrue, H5 ; auto ~.
      rewrite H5 ; auto ~.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))) ; auto ~.
      rewrite <- StageSetProperties.ub_le_1 ; auto ~.
      intros ; apply CalculusProperties.svalueb_iff in Heqb.
      rewrite MP.ssubst_eassign ; destruct H4.
      destruct m ; [rewrite H7 ; auto ~|].
      unfold eq_ssubst_2 in H7.
      rewrite EqNth in H7 ; rewrite H7 ; auto ~.

      (* Case not svalue 0 e1 *)
      destruct H ; apply Nat.max_lub_iff in H ; auto ~ ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto ~.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto ~.

      rewrite MP.ssubst_bind with (f2:=(fun v1 : T.expr => 
        bind dg e0 (fun v2 : T.expr => cast_eassign dg v1 v2))).
      destruct m ; [rewrite H3 ; auto ~|].
      unfold eq_ssubst_2 in H3.
      rewrite EqNth in H3 ; rewrite H3 ; auto ~.
      intros.
      rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr => 
        cast_eassign dg (ssubst m
        match m with
        | 0 => ss
        | S n =>
            if ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))
            then StageSet.add n ss
            else ss
        end (cast_var (hole_var h)) v2 v) v0)).
      destruct m ; [rewrite H5 ; auto ~ |].
      unfold eq_ssubst_2 in H5.
      remember (ltb h (nth 0 bs 0 + booker e2 0)) ; destruct b ;
      symmetry in Heqb0.
      assert(ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0)) = true) as LtbTrue.
      apply leb_iff ; apply leb_iff in Heqb0 ; omega.
      rewrite LtbTrue, H5 ; auto ~.
      rewrite H5 ; auto ~.
      destruct (ltb h (nth 0 bs 0 + (booker e1 0 + booker e2 0))) ; auto ~.
      rewrite <- StageSetProperties.ub_le_1 ; auto ~.
      intros ; rewrite MP.ssubst_eassign ; auto ~.

      destruct H ; apply Nat.max_lub_iff in H ; destruct H.
      destruct IHe1 with (m:=m) ; destruct IHe2 with (m:=m) ; auto ~.
      unfold map_iter_booker ; rewrite List2Properties.length_map_iter ; auto ~.
      destruct H5 ; destruct H3.
      apply EqMerge ; auto ~.
      split ; auto ~.
      apply Nat.max_lub_iff ; omega.
      inversion H0.

    (* EBox *)
    specialize (IHe (0::bs) (dg_ebox dg) (dg::dgs) h v) ;
    specialize (booker_length e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros BKLength.
    specialize (depth_length e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros DpthLength1.
    specialize (eq_ssubst_2_fill_ge_1 e bs dg dgs) ; intros EqFill1.
    specialize (eq_ssubst_2_fill_ge_2 e bs dg dgs) ; intros EqFill2.
    destruct (trans e) ; intros.
    destruct t ; simpl in *|-* ; intros.

      (* depth e = 0 *)
      unfold eq_ssubst_2 ; repeat(split) ; intros.

      rewrite MP.ssubst_ret, MP.ssubst_ebox ;
      rewrite DpthLength1 in *|-* ;
      rewrite BKLength in *|-* ; simpl in *|-* ;
      destruct IHe with (m:=S m) ; auto ~ ; try(omega).
      unfold eq_ssubst_2 in H1 ; simpl in H1 ;
      destruct m ; rewrite H1 ; auto ~ ; [
      rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto ~ | ] ;
      destruct m ; auto ~ ; destruct (ltb h (nth 0 bs 0 + 0)) ; auto ~ ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto ~) ;
      try(apply StageSetProperties.ub_le_2 with (m:=(S (S m))) ; auto ~) ;
      try(rewrite StageSetProperties.ub_le_2 with (m:=1) ; auto ~ ; omega).

      constructor.

      rewrite MP.ssubst_ebox ;
      rewrite DpthLength1 in *|-* ;
      rewrite BKLength in *|-* ; simpl in *|-* ;
      destruct IHe with (m:=S m) ; auto ~ ; try(omega) ;
      unfold eq_ssubst_2 in H2 ; simpl in H2 ;
      destruct m ; rewrite H2 ; auto ~ ; [
      rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto ~ | ] ;
      destruct m ; auto ~ ; destruct (ltb h (nth 0 bs 0 + 0)) ; auto ~ ;
      try(rewrite <- StageSetProperties.ub_le_1 ; auto ~) ;
      try(apply StageSetProperties.ub_le_2 with (m:=(S (S m))) ; auto ~) ;
      try(rewrite StageSetProperties.ub_le_2 with (m:=1) ; auto ~ ; omega).
      

      (* depth e > 0 *)
      rewrite DpthLength1 in H.
      destruct IHe with (m:=S m) ; auto ~ ; try(omega).
      repeat(split) ; intros ; simpl in *|-*.
      destruct H1 ; clear H2 IHe.
      rewrite BKLength ; rewrite BKLength in H0.
      inversion H1 ; subst ; simpl in *|-*.
      
      specialize (EqFill1 h v).
      destruct t ; [contradiction|].
      apply EqFill1 ; auto ~.

      specialize (EqFill2 h v).
      destruct t ; [contradiction|].
      apply EqFill2 ; auto ~.
      
      destruct H1 ; inversion H1 ; subst ; auto ~ ; constructor.
      inversion H2 ; subst.
      apply CalculusProperties.depth_svalue in H5 ; exfalso ; omega.

    (* EUnbox *)
    destruct bs ; simpl in *|-*.
    destruct (List2.hd_cons dgs dg_empty).
    specialize (IHe nil d l h v) ; destruct (trans e).
    intros ; destruct m ; exfalso ; omega.

    destruct (List2.hd_cons dgs dg_empty).
    specialize (IHe bs d l h v).
    specialize (context_stack_not_nil e bs d l) ; intros CSNotNil.
    specialize (depth_length e bs d l) ; intros DpthLength.
    specialize (booker_length e bs d l) ; intros BKLength.
    destruct (trans e) ; intros.
    destruct m ; [exfalso ; omega| simpl in *|-*].

    unfold eq_ssubst_2 ; repeat(split) ; intros ; simpl in *|-*.
    rewrite MP.ssubst_eunbox, MP.ssubst_evar.

    remember (ltb h (n + 1)).
    destruct b ; symmetry in Heqb ; unfold ltb in Heqb.
    assert(CRaw.BindingSet.rho m
           (StageSet.remove (S m) (StageSet.add m ss)) = false) as RhoFalse.
    rewrite BindingSetProperties.rho_false_mem ; auto ~.
    rewrite StageSetProperties.remove_mem_1 ; auto ~.
    apply StageSetProperties.add_mem_3 ; auto ~.
    simpl ; rewrite RhoFalse ; simpl ; rewrite andb_false_r ; constructor.
    apply leb_iff_conv in Heqb.
    assert(beq_nat (hole_var h) (hole_var n) = false) as BeqFalse1.
    apply beq_nat_false_iff ; unfold hole_var ; omega.
    rewrite BeqFalse1 ; simpl ; constructor. 

    destruct IHe with (m:=m) ; auto ~ ; try(omega).
    destruct bs ; simpl in *|-*.
    exfalso ; omega.
    destruct t ; simpl.
    assert((e0, n) = (e0, (n+length(tl ((e0, n) :: nil)))%nat)) as Eq1.
    rewrite plus_0_r ; auto ~.
    simpl tl in Eq1.
    rewrite Eq1 ; clear Eq1.
    constructor ; auto ~.
    rewrite BKLength in H0 ; simpl in H0.
    repeat(constructor ; auto ~).
    constructor ; auto ~.
    assert((e0, n) = (e0, (n+length(tl ((e0, n) :: nil)))%nat)) as Eq1.
    rewrite plus_0_r ; auto ~.
    simpl tl in Eq1.
    rewrite Eq1 ; clear Eq1.
    constructor ; auto ~.
    rewrite BKLength in H0 ; simpl in H0 ; auto ~.
    constructor.
    destruct H1 ; auto ~.
    inversion H0.

    (* ERun *)
    specialize (IHe bs (dg_erun dg) dgs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ~.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_erun dg v0)) ; 
    intros.
    rewrite H1 ; auto ~.
    rewrite MP.ssubst_erun ; reflexivity.
    destruct H1 ; auto ~.
    inversion H0.

    (* ELift *)
    specialize (IHe bs (dg_elift dg) dgs h v) ;
    destruct (trans e) ; intros ;
    unfold eq_ssubst_2 ; repeat(split) ; intros ;
    destruct IHe with (m:=m) ; auto ~.
    rewrite MP.ssubst_bind with (f2:= (fun v0 : T.expr => cast_elift dg v0)) ; 
    intros.
    rewrite H1 ; auto ~.
    rewrite MP.ssubst_elift ; reflexivity.
    destruct H1 ; auto ~.
    inversion H0.
  Qed.

End EqSubstProperties2.

Module EqSubstProperties (R:Replacement) (S:ReplacementCalculus R)
    (T:StagedCalculus) (DG:DataGathering R S) 
    (DGP:DataGatheringPredicates R S DG)
    (DGR:DataGatheringRequirements R S DG DGP)
    (M:Monad R S T DG) (MP:MonadStepProperties R S T DG DGP DGR M)
    (TrSP:TranslationStaticProperties R S T DG DGP DGR M MP.Translation).

  Module E3 := EqSubstProperties3 R S T DG DGP DGR M MP TrSP.
  Module E2 := EqSubstProperties2 R S T DG DGP DGR M MP TrSP.
  Module Translation := MP.Translation.
  Module StaticProperties := TrSP.
  Module ContextStaticProperties := TrSP.ContextStaticProperties.
  Module CalculusProperties := E2.CalculusProperties.
  Module BindingSetProperties := E2.BindingSetProperties.
  Import E3.
  Import E2.
  Import StaticProperties.
  Import Translation.
  Import S.
  Import M.
  Import DG.

  Definition eq_ssubst (n:nat) (h:CRaw.var) 
      (m:nat) (v:T.expr) (b:nat) (u1 u2:T.expr) : Prop :=
      forall (ss:StageSet.t),
      StageSet.ub n ss = true ->
      (M.ssubst n (match n with
	  | S (S n) => if ltb h (b + m) 
       		then StageSet.add (S n) ss else ss
	  | _ => ss
          end) (M.cast_var (hole_var h)) u1 v) = u2.

  Definition eq_context_ssubst := ContextStaticProperties.congr_context_ssubst eq_ssubst.
  Definition eq_stack_ssubst := ContextStaticProperties.congr_stack_ssubst eq_ssubst.

  Lemma eq_ssubst_3_eq_ssubst:
    forall (e:T.expr) (b m n:nat) (h:S.var) (v:T.expr),
    eq_ssubst_3 n h m v b e e ->
    eq_ssubst n h m v b e e.
  Proof.
    intros ; unfold eq_ssubst ; intros.
    unfold eq_ssubst_3 in H.
    destruct n ; try(apply H ; auto ~ ; constructor ; fail).
    destruct n ; try(apply H ; auto ~ ; constructor ; fail).
    remember (ltb h (b + m) && leb b h) ;
    symmetry in Heqb0 ; destruct b0.
    apply andb_true_iff in Heqb0 ; destruct Heqb0.
    rewrite H1 ; apply H ; auto ~ ; constructor.
    apply H ; auto ~ ; try(constructor).
    destruct (ltb h (b + m)) ; auto ~.
    rewrite <- StageSetProperties.ub_le_1 ; auto ~.
  Qed.

  Lemma eq_context_ssubst_3_eq_ssubst:
    forall (c:Context.t) (b1 b2 m n:nat) (h:S.var) (v:T.expr),
    eq_context_ssubst_3 n h m v b1 b2 c c ->
    eq_context_ssubst n h m v b1 b2 c c.
  Proof.
    induction c ; intros.
    constructor.
    inversion H ; subst ; constructor.
    apply eq_ssubst_3_eq_ssubst ; auto ~.
    apply IHc ; auto ~.
  Qed.

  Lemma eq_stack_ssubst_3_eq_ssubst:
    forall (cs:Context.t_stack) (bs:list nat) (b n:nat) (h:S.var) (v:T.expr),
    eq_stack_ssubst_3 n h v bs b cs cs ->
    eq_stack_ssubst n h v bs b cs cs.
  Proof.
    induction cs ; intros.
    constructor.
    inversion H ; subst ; constructor.
    apply eq_context_ssubst_3_eq_ssubst ; auto ~.
    apply eq_context_ssubst_3_eq_ssubst ; auto ~.
    apply IHcs ; auto ~.
  Qed.

  Lemma eq_ssubst_gt:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t) (h:S.var) (v:T.expr),
    let n := depth e in
    let (e0, cs) := trans e bs dg dgs in
    forall (m:nat), 
    n < m < length bs ->
    eq_ssubst m h (booker e 0) v (nth 0 bs 0) e0 e0 /\
    eq_stack_ssubst (pred m) h v 
                       (List.tl bs) (List.hd 0 bs) cs cs /\
    (svalue 0 e -> eq_ssubst m h (booker e 0) v (nth 0 bs 0) 
      (phi e bs dg dgs) (phi e bs dg dgs)).
  Proof.
    intros ; 
    specialize (eq_ssubst_3_gt e bs dg dgs h v) ; intros P.
    destruct (trans e bs) ; intros.
    specialize (P m H).
    destruct P.
    destruct H1.
    split.
    apply eq_ssubst_3_eq_ssubst ; auto ~.
    split.
    apply eq_stack_ssubst_3_eq_ssubst ; auto ~.
    intros ; specialize (H2 H3).
    apply eq_ssubst_3_eq_ssubst ; auto ~.
  Qed.

  Lemma eq_ssubst_eq:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t) (h:S.var) (v:T.expr),
    let n := depth e in
    let (e0, cs) := trans e bs dg dgs in
    0 < n < length bs ->
    nth (pred n) bs 0 + booker e (pred n) <= h ->
    eq_ssubst n h (booker e 0) v (nth 0 bs 0) e0 e0 /\
    eq_stack_ssubst (pred n) h v 
                       (List.tl bs) (List.hd 0 bs) cs cs /\
    (svalue 0 e -> eq_ssubst n h (booker e 0) v (nth 0 bs 0) 
      (phi e bs dg dgs) (phi e bs dg dgs)).
  Proof.
    intros ; subst n.
    specialize (booker_length e bs dg dgs) ; intros BKLength.
    specialize (depth_length e bs dg dgs) ; intros DpthLength.
    specialize (eq_ssubst_2_ge e bs dg dgs) ; intros Strong.
    destruct (trans e) ; intros.
    specialize (Strong h v (depth e)) ; simpl in Strong.
    destruct Strong ; auto ~ ; try(omega).
    destruct H2.
    rewrite BKLength in *|-*.

    repeat(split ; intros).

    (* Part 1 *)
    unfold eq_ssubst ; unfold eq_ssubst_2 in H1 ; intros.
    destruct (depth e) ; [exfalso ; omega|].
    destruct n ; auto ~ ; simpl in *|-*.
    assert(ltb h (nth 0 bs 0 + length (nth 0 t nil)) = false) as False1.
    apply leb_iff_conv ; omega.
    rewrite False1 in H1 ; auto ~.

    (* Part 2 *)
    rewrite DpthLength in *|-*.
    clear BKLength DpthLength H1 H3.
    generalize dependent bs.
    induction t ; simpl in *|-* ; intros.
    constructor.
    destruct bs ; simpl in *|-* ; [exfalso; omega|].
    inversion H2 ; subst ;
    constructor ; simpl in *|-* ; auto ~.

    clear IHt H2.
    induction a.
    constructor.
    inversion H5 ; subst ; simpl in *|-* ; auto ~.
    constructor ; auto ~.
    apply IHa ; auto ~ ; omega.
    

    clear IHt H2 H10.
    induction a.
    constructor.
    inversion H7 ; subst ; simpl in *|-* ; auto ~.
    constructor ; auto ~.
    unfold eq_ssubst ; unfold eq_ssubst_2 in H4 ; intros.
    destruct (length cs1) ; auto ~.
    assert(ltb h (b1 + length c1') = false) as False1.
    apply leb_iff_conv ; omega.
    rewrite False1 in H4 ; auto ~.

    specialize (IHt (b1::bs0)).
    simpl in IHt ; apply IHt ; auto ~.
    omega.

    (* Part 3 *)
    unfold eq_ssubst ; unfold eq_ssubst_2 in H3 ; intros.
    specialize (H3 H4).
    destruct (depth e) ; [exfalso ; omega|].
    destruct n ; auto ~ ; simpl in *|-*.
    assert(ltb h (nth 0 bs 0 + length (nth 0 t nil)) = false) as False1.
    apply leb_iff_conv ; omega.
    rewrite False1 in H3 ; auto ~.
  Qed.

End EqSubstProperties.

Module AdminSubstProperties (R:Replacement) (S:ReplacementCalculus R)
    (T:StagedCalculus) (DG:DataGathering R S) 
    (DGP:DataGatheringPredicates R S DG)
    (DGR:DataGatheringRequirements R S DG DGP)
    (M:Monad R S T DG) (MP:MonadStepProperties R S T DG DGP DGR M)
    (TrSP:TranslationStaticProperties R S T DG DGP DGR M MP.Translation).

  Module E := EqSubstProperties R S T DG DGP DGR M MP TrSP.
  Module E2 := E.E2.
  Module E3 := EqSubstProperties3 R S T DG DGP DGR M MP TrSP.
  Module Translation := MP.Translation.
  Module StaticProperties := TrSP.
  Module ContextStaticProperties := TrSP.ContextStaticProperties.
  Module CalculusProperties := E.CalculusProperties.
  Module BindingSetProperties := E.BindingSetProperties.
  Import E3.
  Import E2.
  Import E.
  Import StaticProperties.
  Import Translation.
  Import S.
  Import M.
  Import DG.

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

  Definition admin_context_ssubst := ContextStaticProperties.congr_context_ssubst admin_ssubst.
  Definition admin_stack_ssubst := ContextStaticProperties.congr_stack_ssubst admin_ssubst.

  Lemma admin_fill_ssubst_1:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) (dg_ebox dg) (dg::dgs) in
    match cs with
    | c1 :: nil => 
      match c1 with
      | nil => False
      | (eh, h) :: c1' => let b := hd 0 bs in
        forall (v e2:T.expr) (c2:Context.t),
        admin_context_ssubst 0 h 0 v b 0 c1' c2 ->
        admin_ssubst 1 h (booker e 0) v 0 e1 e2 ->
        admin_ssubst 0 h (booker e 1) v b
        (Context.fill dg c1' (ret dg (cast_ebox dg e1))) 
        (Context.fill dg c2 (ret dg (cast_ebox dg e2)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (context_stack_not_nil e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros CSNotNil.
    specialize (length_h_match e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros LengthHMatch.
    destruct (trans e (0 :: bs) (dg_ebox dg) (dg::dgs)).
    destruct t ; auto ~.
    destruct t0 ; auto ~.
    destruct t ; auto ~.
    exfalso ; apply CSNotNil ; simpl ; auto ~.
    
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
    rewrite MP.ssubst_ret, MP.ssubst_ebox ; auto ~.
    repeat(constructor).
    apply H1 ; auto ~.
    simpl in *|-*.
    rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto ~.
    destruct p ; subst ; intros.
    assert(Tmp4 := Tmp3).
    apply lt_le_weak in Tmp3.
    inversion H0 ; subst ; simpl.
    unfold admin_ssubst ; intros.
    simpl in *|-*.
    assert(~ ((e1, v) :: t = nil \/ False)) as Tmp2.
    unfold not ; clear ; intros ; destruct H ; auto ~ ; inversion H.
    specialize (IHt Tmp2 Tmp3 v0 e2 c0 H6 H1).

    assert(beq_var (hole_var v) (hole_var (length t)) = false) as BeqFalse1.
    subst ; unfold hole_var ; apply beq_nat_false_iff ; 
    generalize Tmp4 ; clear ; intros ; omega.

    rewrite MP.ssubst_bind with (f2:= fun v2 =>
        (cast_eapp dg (cast_eabs dg (cast_var (hole_var (length t)))
         (ssubst 0 ss (cast_var (hole_var v)) 
           (Context.fill dg t (ret dg (cast_ebox dg e0))) v0)) v2)); auto ~.
    constructor ; auto ~ ; intros.
    constructor ; [| constructor].
    constructor.
    apply IHt ; auto ~ ; intros.
    intros.
    rewrite MP.ssubst_eapp, MP.ssubst_eabs, BeqFalse1 ; auto ~.
  Qed.

  Lemma admin_fill_ssubst_2_strong:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) (dg_ebox dg) (dg::dgs) in
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
          (Context.fill dg c1 (ret dg (cast_ebox dg e1))) v) 
          (Context.fill dg c2 (ret dg (cast_ebox dg e2)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (depth_length e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros DpthLength1.
    specialize (context_stack_not_nil e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros CSNotNil.
    specialize (length_h_match e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros LengthHMatch.
    specialize (booker_length e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros BookerLength.
    destruct (trans e (0 :: bs) (dg_ebox dg) (dg::dgs)).
    destruct t ; auto ~.
    destruct t0 ; auto ~.
    destruct t1 ; auto ~.
    destruct t0 ; auto ~.
    exfalso ; apply CSNotNil ; simpl ; auto ~.

    rewrite BookerLength ; simpl.
    clear LengthHMatch BookerLength CSNotNil.
    induction t.
    destruct p ; intros.
    inversion H2 ; subst ; simpl in *|-*.
    rewrite MP.ssubst_ret, MP.ssubst_ebox ; repeat(constructor) ; auto ~.

    simpl in *|-*.
    destruct p ; intros.
    inversion H2 ; subst ; simpl in *|-*.
    rewrite DpthLength1 in H ; destruct bs.
    exfalso ; generalize H ; clear ; simpl ; intros ; omega.
    specialize (IHt DpthLength1 v0 e2 c0) ; simpl in *|-*.
    case_beq_nat v (length t).
      rewrite MP.ssubst_bind with (f2:= fun v2 =>
        (cast_eapp dg (cast_eabs dg (cast_var (hole_var (length t)))
         (ssubst 1 (StageSet.add 1 ss) (cast_var (hole_var (length t))) 
           (Context.fill dg t (ret dg (cast_ebox dg e0))) v0)) v2)); auto ~.
      constructor ; auto ~ ; intros.
      repeat(constructor).
      apply IHt ; auto ~.
      rewrite StageSetProperties.add_mem_4 ; auto ~.
      rewrite <- StageSetProperties.ub_le_1 ; auto ~.
      assert(ltb (length t) (S (length t)) = true).
      clear ; unfold ltb ; apply leb_iff ; omega.
      rewrite H4 in H3 ; clear H4.
      assert(ltb (length t) (length t) = false).
      clear ; unfold ltb ; apply leb_iff_conv ; omega.
      rewrite H4 ; clear H4 ; auto ~.
      intros.
      rewrite MP.ssubst_eapp, MP.ssubst_eabs ; auto ~.
      rewrite <- beq_nat_refl ; auto ~.

      assert(ltb v (length t) = ltb v (S (length t))) as LtbEq.
      generalize E ; clear ; intros ; unfold ltb.
      remember (leb (S v) (S (length t))).
      destruct b ; symmetry in Heqb.
      apply leb_iff ; apply leb_iff in Heqb ; omega.
      apply leb_iff_conv ; apply leb_iff_conv in Heqb ; omega.
      rewrite LtbEq in IHt ; clear LtbEq.

      rewrite MP.ssubst_bind with (f2:= fun v2 =>
        (cast_eapp dg (cast_eabs dg (cast_var (hole_var (length t)))
         (ssubst 1 ss (cast_var (hole_var v)) 
           (Context.fill dg t (ret dg (cast_ebox dg e0))) v0)) v2)); auto ~.
      constructor ; auto ~ ; intros.
      repeat(constructor).
      apply IHt ; auto ~.
      intros.
      rewrite MP.ssubst_eapp, MP.ssubst_eabs ; auto ~.
      assert(beq_var (hole_var v) (hole_var (length t)) = false).
      generalize E ; clear ; intros ; unfold hole_var ; 
      apply beq_nat_false_iff ; omega.
      rewrite H4 ; auto ~.
  Qed.

  Lemma admin_fill_ssubst_2:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) (dg_ebox dg) (dg::dgs) in
    match cs with
    | c1 :: c1' :: nil => 
      match c1' with
      | nil => False
      | (eh, h) :: c1'' => let b := hd 0 bs in
        forall (v e2:T.expr) (c2:Context.t),
        admin_context_ssubst (pred (depth e)) h (length c1'') v b 0 c1 c2 ->
        admin_ssubst (depth e) h (booker e 0) v 0 e1 e2 ->
        admin_ssubst (pred (depth e)) h (booker e 1) v b
        (Context.fill dg c1 (ret dg (cast_ebox dg e1)))
        (Context.fill dg c2 (ret dg (cast_ebox dg e2)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (admin_fill_ssubst_2_strong e bs dg dgs H) ; intros Strong.
    specialize (depth_length e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros DpthLength1.
    specialize (booker_length e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros BookerLength.
    destruct (trans e (0 :: bs) (dg_ebox dg) (dg::dgs)).
    destruct t ; auto ~.
    destruct t0 ; auto ~.
    destruct t1 ; auto ~.
    destruct t0 ; auto ~.
    destruct p ; intros ; auto ~.
    rewrite DpthLength1 in *|-* ; simpl in *|-* ; auto ~.
    rewrite BookerLength in *|-* ; simpl in *|-* ; auto ~.
    unfold admin_ssubst ; simpl ; intros.
    apply Strong ; auto ~.
    apply H1 ; auto ~.
    rewrite StageSetProperties.ub_le_2 with (m:=1) ; auto ~.
  Qed.

  Lemma admin_fill_ssubst_3_strong:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) (dg_ebox dg) (dg::dgs) in
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
            (Context.fill dg c1 (ret dg (cast_ebox dg e1))) v) 
            (Context.fill dg c2 (ret dg (cast_ebox dg e2)))
	end
    | _ => True
    end.
  Proof.
    intros.
    specialize (depth_length e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros DpthLength1.
    specialize (context_stack_not_nil e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros CSNotNil.
    specialize (length_h_match e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros LengthHMatch.
    specialize (booker_length e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros BookerLength.
    destruct (trans e (0 :: bs) (dg_ebox dg) (dg::dgs)).
    destruct t ; auto ~.
    destruct t0 ; auto ~.
    destruct t1 ; auto ~.
    specialize (context_shift_not_nil (t :: t0 :: t1 :: t2)) ; intros CShiftNotNil.
    destruct (Context.shift).
    destruct t3 ; auto ~.
    assert(length (t :: t0 :: t1 :: t2) > 0).
    simpl ; omega.
    specialize (CShiftNotNil H0 CSNotNil) ; destruct CShiftNotNil.
    apply H1 ; auto ~.

    rewrite BookerLength ; rewrite BookerLength ; simpl.
    clear LengthHMatch BookerLength CShiftNotNil CSNotNil.
    induction t.
    destruct p ; intros.
    inversion H2 ; subst ; rewrite DpthLength1 in *|-* ; simpl in *|-*.
    rewrite MP.ssubst_ret, MP.ssubst_ebox ; repeat(constructor) ; auto ~.

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
         destruct (ltb (length t) (n + length t0)) ; auto ~.
         apply StageSetProperties.add_add.
      rewrite MP.ssubst_bind with (f2:= fun v2 =>
        (cast_eapp dg (cast_eabs dg (cast_var (hole_var (length t)))
         (ssubst (S (S (length t2)))
         (if ltb (length t) (n + length t0) 
         then StageSet.add (S (length t2)) (StageSet.add (S (S (length t2))) ss) 
         else (StageSet.add (S (S (length t2))) ss))
           (cast_var (hole_var (length t))) 
           (Context.fill dg t (ret dg (cast_ebox dg e0))) v0)) v2)); auto ~.
      constructor ; auto ~ ; intros.
      repeat(constructor).
      apply IHt ; auto ~.
      rewrite StageSetProperties.add_mem_4 ; auto ~.
      rewrite <- StageSetProperties.ub_le_1 ; auto ~.
      assert(ltb (length t) (S (length t)) = true).
      clear ; unfold ltb ; apply leb_iff ; omega.
      rewrite H4 in H3 ; clear H4.
      assert(ltb (length t) (length t) = false).
      clear ; unfold ltb ; apply leb_iff_conv ; omega.
      rewrite H4 ; clear H4 ; auto ~.
      rewrite <- Eq1 in H3 ; auto ~.
      intros.
      rewrite MP.ssubst_eapp, MP.ssubst_eabs ; auto ~.
      rewrite <- beq_nat_refl ; auto ~.
      destruct (ltb (length t) (n + length t0)) ;
      auto ~ ; rewrite Eq1 ; auto ~.

      assert(ltb v (length t) = ltb v (S (length t))) as LtbEq.
      generalize E ; clear ; intros ; unfold ltb.
      remember (leb (S v) (S (length t))).
      destruct b ; symmetry in Heqb.
      apply leb_iff ; apply leb_iff in Heqb ; omega.
      apply leb_iff_conv ; apply leb_iff_conv in Heqb ; omega.
      rewrite LtbEq in IHt ; clear LtbEq.

      rewrite MP.ssubst_bind with (f2:= fun v2 =>
        (cast_eapp dg (cast_eabs dg (cast_var (hole_var (length t)))
          (ssubst (S (S (length t2))) 
          (if ltb v (n + length t0) then StageSet.add (S (length t2)) ss else ss)
          (cast_var (hole_var v)) 
           (Context.fill dg t (ret dg (cast_ebox dg e0))) v0)) v2)); auto ~.
      constructor ; auto ~ ; intros.
      repeat(constructor).
      apply IHt ; auto ~.
      intros.
      rewrite MP.ssubst_eapp, MP.ssubst_eabs ; auto ~.
      assert(beq_var (hole_var v) (hole_var (length t)) = false).
      generalize E ; clear ; intros ; unfold hole_var ; 
      apply beq_nat_false_iff ; omega.
      rewrite H4 ; auto ~.
  Qed.

  Lemma admin_fill_ssubst_3:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) (dg_ebox dg) (dg::dgs) in
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
          (Context.fill dg c1 (ret dg (cast_ebox dg e1))) 
          (Context.fill dg c2 (ret dg (cast_ebox dg e2)))
	end
    | _ => True
    end.
  Proof.
    intros.
    specialize (depth_length e (0::bs) (dg_ebox dg) (dg::dgs)) ; intros DpthLength1.
    specialize (admin_fill_ssubst_3_strong e bs dg dgs H) ; intros Strong.
    destruct (trans e (0 :: bs)).
    destruct t ; auto ~.
    destruct t0 ; auto ~.
    destruct t1 ; auto ~.
    destruct (Context.shift).
    destruct t3 ; auto ~.
    destruct p ; intros ; auto ~.
    rewrite DpthLength1 in *|-* ; simpl in *|-* ; auto ~.
    unfold admin_ssubst ; simpl ; intros.
    apply Strong ; auto ~.
    unfold admin_ssubst in H1 ; simpl in H1.
    apply H1 ; auto ~.
    destruct (ltb v (hd 0 bs + booker e 1)) ; auto ~.
    rewrite StageSetProperties.add_mem_4 ; auto ~.
    destruct (ltb v (hd 0 bs + booker e 1)) ; [
    rewrite <- StageSetProperties.ub_le_1 ; auto ~ |] ;
    rewrite StageSetProperties.ub_le_2 with (m:=S (S (length t2))) ; auto ~.
  Qed.

  Lemma admin_fill_ssubst:
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) (dg_ebox dg) (dg::dgs) in
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
        (Context.fill dg c1' (ret dg (cast_ebox dg e1))) 
        (Context.fill dg c2 (ret dg (cast_ebox dg e2)))
      end
    | c1 :: c1' :: nil => 
      match c1' with
      | nil => False
      | (eh, h) :: c1'' => let b := hd 0 bs in
        forall (v e2:T.expr) (c2:Context.t),
        admin_context_ssubst (pred (depth e)) h (length c1'') v b 0 c1 c2 ->
        admin_ssubst (depth e) h (booker e 0) v 0 e1 e2 ->
        admin_ssubst (pred (depth e)) h (booker e 1) v b
        (Context.fill dg c1 (ret dg (cast_ebox dg e1))) 
        (Context.fill dg c2 (ret dg (cast_ebox dg e2)))
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
          (Context.fill dg c1 (ret dg (cast_ebox dg e1)))
          (Context.fill dg c2 (ret dg (cast_ebox dg e2)))
	end
    end.
  Proof.
    intros.
    specialize (admin_fill_ssubst_1 e bs dg dgs) ; intros Case1.
    specialize (admin_fill_ssubst_2 e bs dg dgs) ; intros Case2.
    specialize (admin_fill_ssubst_3 e bs dg dgs) ; intros Case3.
    destruct (trans e (0 :: bs)).
    destruct t ; auto ~.
    destruct t0 ; auto ~.
    destruct t ; auto ~.
    destruct p ; intros ; auto ~.
    destruct t1 ; auto ~.
    destruct t0 ; auto ~.
    destruct p ; intros ; auto ~.
    destruct (Context.shift) ; auto ~.
    destruct t3 ; auto ~.
    destruct p ; intros ; auto ~.
  Qed.

  Lemma eq_ssubst_3_admin:
    forall (e:T.expr) (b m n:nat) (h:S.var) (v:T.expr),
    eq_ssubst_3 n h m v b e e ->
    admin_ssubst n h m v b e e.
  Proof.
    intros ; unfold admin_ssubst ; intros.
    unfold eq_ssubst_3 in H.
    destruct n ; try(rewrite H ; auto ~ ; constructor ; fail).
    destruct n ; try(rewrite H ; auto ~ ; constructor ; fail).
    remember (ltb h (b + m) && leb b h) ;
    symmetry in Heqb0 ; destruct b0.
    apply andb_true_iff in Heqb0 ; destruct Heqb0.
    rewrite H2, H ; auto ~ ; constructor.
    rewrite H ; auto ~ ; try(constructor).
    destruct (ltb h (b + m)) ; auto ~.
    rewrite <- StageSetProperties.ub_le_1 ; auto ~.
  Qed.

  Lemma eq_context_ssubst_3_admin:
    forall (c:Context.t) (b1 b2 m n:nat) (h:S.var) (v:T.expr),
    eq_context_ssubst_3 n h m v b1 b2 c c ->
    admin_context_ssubst n h m v b1 b2 c c.
  Proof.
    induction c ; intros.
    constructor.
    inversion H ; subst ; constructor.
    apply eq_ssubst_3_admin ; auto ~.
    apply IHc ; auto ~.
  Qed.

  Lemma eq_stack_ssubst_3_admin:
    forall (cs:Context.t_stack) (bs:list nat) (b n:nat) (h:S.var) (v:T.expr),
    eq_stack_ssubst_3 n h v bs b cs cs ->
    admin_stack_ssubst n h v bs b cs cs.
  Proof.
    induction cs ; intros.
    constructor.
    inversion H ; subst ; constructor.
    apply eq_context_ssubst_3_admin ; auto ~.
    apply eq_context_ssubst_3_admin ; auto ~.
    apply IHcs ; auto ~.
  Qed.

  Lemma eq_ssubst_admin:
    forall (e:T.expr) (b m n:nat) (h:S.var) (v:T.expr),
    eq_ssubst n h m v b e e ->
    admin_ssubst n h m v b e e.
  Proof.
    intros ; unfold admin_ssubst ; intros.
    rewrite H ; auto ~.
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
    apply eq_ssubst_admin ; auto ~.
    apply IHc ; auto ~.
  Qed.

  Lemma eq_stack_ssubst_admin:
    forall (cs:Context.t_stack) (bs:list nat) (b n:nat) (h:S.var) (v:T.expr),
    eq_stack_ssubst n h v bs b cs cs ->
    admin_stack_ssubst n h v bs b cs cs.
  Proof.
    induction cs ; intros.
    constructor.
    inversion H ; subst ; constructor.
    apply eq_context_ssubst_admin ; auto ~.
    apply eq_context_ssubst_admin ; auto ~.
    apply IHcs ; auto ~.
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
    apply H ; auto ~.
    destruct n.
    apply H ; auto ~.
    apply H ; auto ~.
    rewrite StageSetProperties.add_mem_4 ; auto ~.
    rewrite <- StageSetProperties.ub_le_1 ; auto ~.
    assert(ltb h (b + S m) = ltb h (b + m)) as Eq1.
    generalize E ; clear ; intros.
    remember (ltb h (b + m)) ; destruct b0 ; symmetry in Heqb0 ;
    [apply leb_iff ; apply leb_iff in Heqb0 | 
    apply leb_iff_conv ; apply leb_iff_conv in Heqb0] ; omega.
    rewrite Eq1 ; apply H ; auto ~.
  Qed.

  Lemma admin_ssubst_m_ge:
    forall (e1 e2:T.expr) (b:nat) (h:S.var) (v:T.expr) (n m p:nat),
    admin_ssubst n h m v b e1 e2 -> 
    m <= p -> admin_ssubst n h p v b e1 e2.
  Proof.
    intros.
    induction H0 ; auto ~.
    apply admin_ssubst_m_Sm ; auto ~.
  Qed.

  Lemma admin_context_ssubst_m_ge:
    forall (c1 c2:Context.t) (b1 b2:nat) (h:S.var) (v:T.expr) (n m p:nat),
    admin_context_ssubst n h m v b1 b2 c1 c2 -> 
    m <= p -> admin_context_ssubst n h p v b1 b2 c1 c2.
  Proof.
    induction c1 ; intros ; inversion H ; subst ;
    constructor ; auto ~.
    apply admin_ssubst_m_ge with (m:=m) ; auto ~.
    apply IHc1 with (m:=m) ; auto ~.
  Qed.

  Lemma admin_ssubst_sum:
    forall (e1 e2 v:T.expr) (n m1 m2 b1 b2:nat) (h:S.var),
    admin_ssubst n h m1 v b1 e1 e2 ->
    (b1 + m1 = b2 + m2)%nat ->
    admin_ssubst n h m2 v b2 e1 e2.
  Proof.
    unfold admin_ssubst ; intros.
    rewrite <- H0.
    apply H ; auto ~.
  Qed.

  Lemma admin_context_ssubst_sum:
    forall (c1 c2:Context.t) (v:T.expr) (n m1 m2 b1 b2 b3:nat) (h:S.var),
    admin_context_ssubst n h m1 v b1 b3 c1 c2 ->
    (b1 + m1 = b2 + m2)%nat ->
    admin_context_ssubst n h m2 v b2 b3 c1 c2.
  Proof.
    induction c1 ; simpl ; intros ;
    inversion H ; subst ;
    constructor ; auto ~.
    apply admin_ssubst_sum with (m1:=m1) (b1:=b1) ; auto ~.
    apply IHc1 with (m1:=m1) (b1:=b1) ; auto ~.
  Qed.

  Lemma admin_stack_ssubst_merge_1:
    forall (bs:list nat) (dg1 dg2:dg_t) (dgs1 dgs2:list dg_t) (e1 e2 e3:S.expr), 
    let (e1', cs1) := trans e1 (map_iter_booker e2 bs 0) dg1 dgs1 in
    let (e2', cs2) := trans e2 bs dg2 dgs2 in
    let (e3', cs3) := trans e3 (map_iter_booker e2 bs 0) dg1 dgs2 in
    match Context.merge cs1 cs2 with
    | nil => True
    | _ => 
      let (c1, cs1') := Context.shift cs1 in
      let (c4, cs4') := Context.shift (Context.merge cs1 cs2) in
      match c1 with
      | nil => True
      | cons (t_eh, h) c1' => 
        forall (eh:S.expr),
        t_eh = trans_expr eh (0::nil) dg_empty nil ->
        match c1' with
        | nil =>
            admin_stack_ssubst (pred (depth e1)) h (phi eh (0 :: nil) dg_empty nil)
            (tl (map_iter_booker e2 bs 0))
            (hd 0 (map_iter_booker e2 bs 0)) cs1' cs3
        | _ :: _ =>
            admin_stack_ssubst (pred (depth e1)) h (phi eh (0 :: nil) dg_empty nil)
            (tl (map_iter_booker e2 bs 0))
            (hd 0 (map_iter_booker e2 bs 0)) (Context.unshift cs1' c1') cs3
        end ->
        depth e1 = depth e2 ->
        depth e1 < length bs ->
        match c4 with
        | nil => True
        | _ :: nil =>
          admin_stack_ssubst (pred (depth e1)) h (phi eh (0 :: nil) dg_empty nil) (tl bs)
          (hd 0 bs) cs4'
          (Context.merge cs3 cs2)
        | _ :: c4' =>
          admin_stack_ssubst (pred (depth e1)) h (phi eh (0 :: nil) dg_empty nil) (tl bs)
          (hd 0 bs)
          (Context.unshift cs4' c4')
          (Context.merge cs3 cs2)
        end
      end
    end.
    intros.
    specialize (booker_length e2 bs dg2 dgs2) ; intros BKLength.
    specialize (context_stack_not_nil e1 (map_iter_booker e2 bs 0) dg1 dgs1) ; intros CSNotNil1.
    specialize (context_stack_not_nil e2 bs dg2 dgs2) ; intros CSNotNil2.
    specialize (length_h_match e1 (map_iter_booker e2 bs 0) dg1 dgs1) ; intros LengthHMatch.  
    specialize (map_iter_booker_stack e2 bs dg2 dgs2) ; intros MapIterBooker.
    specialize (depth_length e1 (map_iter_booker e2 bs 0) dg1 dgs1) ; intros DpthLength1.
    specialize (depth_length e2 bs dg2 dgs2) ; intros DpthLength2.
    specialize (eq_ssubst_eq e2 bs dg2 dgs2) ; intros EqSsubstEq.
    destruct (trans e1).
    destruct (trans e2).
    destruct (trans e3).
    cases (Context.merge t t0) as t eqn: Merge1 ; auto ~.
    cases (Context.shift t) as t eqn: Shift1.
    cases (Context.shift t0) as t eqn: Shift2.
    cases (Context.shift (t2 :: t3)) as t eqn: Shift4.
    destruct t4 ; auto ~.
    destruct p ; intros.
    rewrite Merge1, ContextStaticProperties.shift_merge_3, 
      <- Shift1, <- Shift2 in Shift4 ; [|
      rewrite DpthLength1, DpthLength2 in H1 ; auto ~].
    inversion Shift4 ; subst ; clear Shift4.
    specialize (EqSsubstEq v (phi eh (0 :: nil) dg_empty nil)).
    remember (E2.Translation.phi) ; simpl in *|-*.
    rewrite MapIterBooker, DpthLength1, DpthLength2, BKLength in *|-*.
    clear MapIterBooker DpthLength1 DpthLength2 BKLength.
    destruct bs ; [exfalso ; clear EqSsubstEq ; simpl in *|-* ; omega |].
    rewrite map_iter_stack_bs in *|-* ; simpl in *|-*.
    assert(length t <= S (length (map_iter_stack t0 bs 1))) as Tmp1.
    generalize H2 ; clear ; simpl ; intros ; unfold map_iter_stack ; 
    rewrite List2Properties.length_map_iter ; omega.
    specialize (LengthHMatch Tmp1) ; clear Tmp1.
    assert(0 < length t0 < S (length bs)) as Tmp1.
    destruct t0 ; clear EqSsubstEq ; simpl in *|-* ; try(omega).
    destruct t ; simpl in H1 ; [inversion Shift1 | inversion H1].
    specialize (EqSsubstEq Tmp1) ; clear Tmp1.
    assert(match pred (length t0) with
             | 0 => n
             | S m => nth m bs 0
             end + length (nth (pred (length t0)) t0 nil) <= v) as Tmp1.
    rewrite <- H1 in *|-*.
    destruct t ; clear EqSsubstEq ; simpl in *|-* ; [inversion Shift1|].
    rewrite LengthHMatch.
    simpl ; destruct (length t8) ; auto ~ ; try(omega).
    rewrite map_iter_stack_nth_indep ; simpl ; auto ~ ; try(omega).
    simpl nth in EqSsubstEq.
    specialize (EqSsubstEq Tmp1) ; clear Tmp1 LengthHMatch.

    assert(length t0 > 0) as P1.
    destruct t0 ; simpl in *|-* ; auto ~ ; try(omega).
    rewrite ContextStaticProperties.merge_nil_r in Merge1.
    inversion Merge1 ; subst ; simpl in H1 ; inversion H1.
    assert(Context.merge t t0 <> nil) as P2.
    rewrite <- Merge1 ; red ; intros ; inversion H.
    clear Merge1.
    destruct EqSsubstEq.
    destruct H3 ; assert(EqSsubstEq := H3) ; clear H H3 H4.
    
    destruct t4 ; simpl in *|-*.

    (* c1' nil *)
    generalize dependent n ; generalize dependent t ;
    generalize dependent t0 ; generalize dependent t1 ;
    generalize dependent t7 ; 
    generalize dependent bs.
    induction t5 ; intros.

    inversion H0 ; subst ; simpl in *|-*.
    specialize (ContextStaticProperties.shift_spec t0) ; intros Spec1.
    rewrite <- Shift2 in Spec1.
    rewrite ContextStaticProperties.unshift_spec, <- Spec1 ; auto ~.
    destruct t6.
    specialize (context_shift_not_nil t0 P1 CSNotNil2) ; intros CShiftNotNil.
    rewrite <- Shift2 in CShiftNotNil.
    destruct CShiftNotNil ; exfalso ; apply H ; auto ~.
    rewrite H1 in *|-* ;
    apply eq_stack_ssubst_admin ; auto ~.

    destruct t6.
    specialize (context_shift_not_nil t0 P1 CSNotNil2) ; intros CShiftNotNil.
    rewrite <- Shift2 in CShiftNotNil.
    destruct CShiftNotNil ; exfalso ; apply H ; auto ~.
    destruct t.
    exfalso ; destruct t0 ; simpl in *|-* ; [apply P2 ; auto ~|inversion H1].
    destruct t7.
    
    destruct t0 ; simpl in *|-*.
    inversion Shift2.
    destruct (Context.shift t7).
    destruct t7.
    destruct t4 ; simpl in *|-*.
    inversion Shift1 ; subst.
    inversion H1 ; subst.
    inversion Shift2.

    (* Induction *)

    destruct bs ; [exfalso ; simpl in *|-* ; omega |].
    destruct t0 ; auto ~.
    simpl in H1 ; inversion H1.
    destruct t1.
    inversion H0.
    simpl.

    assert(admin_stack_ssubst (pred (length t4)) v (phi eh (0 :: nil) dg_empty nil) bs n0
         (Context.unshift (Context.merge t5 t8)
            (p :: t6)) (Context.merge t10 t9)).
    subst ; apply IHt5 ; auto ~ ; try(simpl in *|-* ; omega).
    simpl in CSNotNil2 ; unfold not ; intros ; apply CSNotNil2 ; right ; auto ~.
    simpl in Shift2 ; destruct (Context.shift t9) ; destruct t9 ; 
    inversion Shift2 ; subst ; auto ~.
    destruct t9 ; simpl ; auto ~ ; try(omega) ;
    simpl in Shift2 ; inversion Shift2.
    simpl in CSNotNil1 ; unfold not ; intros ; apply CSNotNil1 ; right ; auto ~.
    simpl in Shift1 ; destruct (Context.shift t4) ; destruct t4 ; 
    inversion Shift1 ; subst ; auto ~.
    simpl in Shift2 ; destruct (Context.shift t9) ; destruct t9 ; 
    inversion Shift2 ; subst ; destruct t4 ; simpl ; red ; intros T ; 
    inversion T.
    simpl in *|-*.
    rewrite map_iter_stack_cs, map_iter_stack_bs in H0.
    inversion H0 ; subst ; auto ~ ; constructor.
    simpl in EqSsubstEq ; inversion EqSsubstEq ; subst ; auto ~ ; constructor.
    clear IHt5.
    
    inversion H ; subst.
    rewrite ContextStaticProperties.unshift_spec in H6.
    apply app_cons_not_nil in H6 ; contradiction.
    
    constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    rewrite map_iter_stack_cs, map_iter_stack_bs in H0.
    remember (E2.Translation.phi) ;
    inversion H0 ; subst ; simpl in *|-* ; auto ~.
    inversion H6 ; subst ; simpl in *|-* ;
    inversion Shift2 ; subst ; inversion H3 ; subst ; simpl in *|-* ;
    apply admin_context_ssubst_sum with (m1:=0) (b1:=(n0 + (S (length t6)))%nat) ;
    auto ~ ; omega.

    destruct (Context.shift t9) ; destruct t9 ; inversion Shift2 ; subst.
    simpl in *|-*.
    inversion H6 ; subst ; clear H6.
    destruct (Context.merge cs1 cs2) ;
    destruct t10 ; simpl in H3 ; inversion H3 ; subst ;
    rewrite ContextStaticProperties.unshift_spec in H6 ;
    apply app_cons_not_nil in H6 ; contradiction.

    simpl in Shift2 ; destruct (Context.shift t9) ; 
    destruct t9 ; inversion Shift2 ; subst.
    remember E2.Translation.phi ; simpl in *|-*.
    inversion H1 ; subst.
    rewrite H5 ; inversion EqSsubstEq ; subst ; auto ~.
    assert((length t9) <= (length c1)).
    apply ContextStaticProperties.congr_context_ssubst_length in H7.
    destruct t10 ; simpl in *|-*.
    inversion H6 ; subst ; omega.
    inversion H6 ; subst.
    rewrite app_length in H7 ; omega.
    apply admin_context_ssubst_m_ge with (m:=length t9) ; auto ~.
    apply eq_context_ssubst_admin ; auto ~.

    rewrite H3, H6 ; auto ~.
    constructor ; auto ~.
    
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    rewrite map_iter_stack_cs, map_iter_stack_bs in H0.
    remember (E2.Translation.phi) ; inversion H0 ; subst ; simpl in *|-* ; auto ~.
    destruct (Context.shift t9).
    inversion H4 ; subst ; simpl in *|-*.
    inversion Shift2 ; subst.
    apply ContextStaticProperties.congr_context_ssubst_length in H7 ; auto ~ ; rewrite H7 in *|-* ; auto ~.
    apply admin_context_ssubst_sum with (m1:=0) (b1:=(n0 + (length c2))%nat) ;
    auto ~ ; omega.

    destruct (Context.shift t9) ; destruct t9 ; inversion Shift2 ; subst.
    simpl in *|-* ; clear Shift2.
    inversion H4 ; subst ; clear H4.
    assert(length c1 = length t9 + length c1'0)%nat.
    apply ContextStaticProperties.congr_context_ssubst_length in H7 ; rewrite app_length in H7.
    rewrite H7.
    assert(length c1'0 = length c2'0).
    inversion H15 ; subst.
    apply ContextStaticProperties.congr_context_ssubst_length in H10 ; auto ~.
    apply ContextStaticProperties.congr_context_ssubst_length in H12 ; auto ~.
    omega.
    apply admin_context_ssubst_sum with (m1:=(length c1'0)) (b1:=(n0 + (length t9))%nat) ;
    auto ~ ; omega.

    simpl in Shift2 ; destruct (Context.shift t9) ; 
    destruct t9 ; inversion Shift2 ; subst.
    remember (E2.Translation.phi) ; simpl in *|-*.
    inversion H1 ; subst.
    rewrite H6 ; inversion EqSsubstEq ; subst ; auto ~.
    assert((length t9) <= (length c1)).
    apply ContextStaticProperties.congr_context_ssubst_length in H7.
    destruct t10 ; simpl in *|-*.
    inversion H4 ; subst ; omega.
    inversion H4 ; subst.
    rewrite app_length in H7 ; omega.
    apply admin_context_ssubst_m_ge with (m:=length t9) ; auto ~.
    apply eq_context_ssubst_admin ; auto ~.
    
    rewrite H3, H4 ; auto ~.

    (* c1' not nil *)
    rewrite ContextStaticProperties.merge_unshift_1 ; auto ~.

    rewrite ContextStaticProperties.unshift_spec in *|-*.
    generalize dependent n ; generalize dependent t ;
    generalize dependent t0 ; generalize dependent t1 ;
    generalize dependent t7 ; 
    generalize dependent bs.
    induction t5 ; intros.

    inversion H0 ; subst.
    simpl in *|-*.
    destruct t0 ; simpl in *|-* ; [exfalso ; omega|].
    destruct bs ; [exfalso ; simpl in *|-* ; omega |].
    rewrite map_iter_stack_cs, map_iter_stack_bs in H.
    inversion H ; subst ; clear H.
    destruct t ; simpl in Shift1 ; [inversion Shift1|].
    simpl in *|-*.
    destruct (Context.shift t5) ; destruct t5 ; 
    inversion Shift1 ; subst.
    destruct t1 ; simpl in *|-* ; [|inversion H1].
    inversion Shift2 ; subst ; simpl in *|-*.
    constructor ; auto ~.
    rewrite app_comm_cons.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    rewrite plus_0_r in *|-* ; auto ~.
    inversion EqSsubstEq ; subst ; auto ~.
    apply eq_context_ssubst_admin ; auto ~.

    (* Induction *)
    destruct bs ; [exfalso ; simpl in *|-* ; omega |].
    destruct t.
    simpl in Shift1 ; inversion Shift1.
    destruct t0 ; auto ~.
    simpl in H1 ; inversion H1.
    destruct t1.
    inversion H0.
    destruct t7.

    simpl in Shift2.
    destruct (Context.shift t9) ; destruct t9 ; 
    inversion Shift2 ; subst.
    destruct t8 ; simpl in H1 ; [|inversion H1].
    simpl in *|-*.
    rewrite ContextStaticProperties.merge_nil_r in *|-*.
    inversion Shift1.

    simpl.
    assert(admin_stack_ssubst (pred (length t8)) v (phi eh (0 :: nil) dg_empty nil) bs n0
         (Context.merge (t5 ++ (p :: t4 ++ t6) :: nil) t11)
         (Context.merge t10 t9)).
    subst ; apply IHt5 ; auto ~ ; try(simpl in *|-* ; omega).
    simpl in CSNotNil2 ; unfold not ; intros ; apply CSNotNil2 ; right ; auto ~.
    simpl in Shift2 ; destruct (Context.shift t9) ; destruct t9 ; 
    inversion Shift2 ; subst ; auto ~.
    destruct t9 ; simpl ; auto ~ ; try(omega) ;
    simpl in Shift2 ; inversion Shift2.
    simpl in CSNotNil1 ; unfold not ; intros ; apply CSNotNil1 ; right ; auto ~.
    simpl in Shift1 ; destruct (Context.shift t8) ; destruct t8 ; 
    inversion Shift1 ; subst ; auto ~.
    simpl in Shift2 ; destruct (Context.shift t9) ; destruct t9 ; 
    inversion Shift2 ; subst ; destruct t8 ; simpl ; red ; intros T ; 
    inversion T.
    simpl in *|-*.
    rewrite map_iter_stack_cs, map_iter_stack_bs in H0.
    inversion H0 ; subst ; auto ~ ; constructor.
    simpl in EqSsubstEq ; inversion EqSsubstEq ; subst ; auto ~ ; constructor.
    clear IHt5.

    rewrite <- ContextStaticProperties.unshift_spec.
    rewrite <- ContextStaticProperties.unshift_spec in H.
    inversion H ; subst.
    apply ContextStaticProperties.merge_nil in H6.
    destruct H6.
    rewrite ContextStaticProperties.unshift_spec in H3.
    symmetry in H3 ; apply app_cons_not_nil in H3.
    contradiction.

    constructor ; auto ~.
    (* Start duplication part *)
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    rewrite <- app_comm_cons in H0.
    rewrite map_iter_stack_cs, map_iter_stack_bs in H0.
    remember (E2.Translation.phi) ; inversion H0 ; subst ; simpl in *|-* ; auto ~.
    apply app_cons_not_nil in H11 ; contradiction.
    destruct (Context.shift t9) ; destruct t9 ; inversion Shift2 ; subst.
    simpl in *|-* ; clear Shift2.
    assert(length c1 = length t9 + length c1')%nat.
    rewrite ContextStaticProperties.unshift_spec in H3.
    apply ContextStaticProperties.congr_context_ssubst_length in H7.
    rewrite H7.
    inversion H6 ; subst.
    rewrite app_length.
    apply ContextStaticProperties.merge_nil in H8 ; destruct H8 ; subst.
    inversion H14 ; subst.
    apply ContextStaticProperties.congr_context_ssubst_length in H9 ; rewrite H9 ; omega.
    apply admin_context_ssubst_sum with (m1:=length c1') (b1:=(n0 + (length t9))%nat) ;
    auto ~ ; try(omega).
    
    simpl in Shift2 ; destruct (Context.shift t9) ; 
    destruct t9 ; inversion Shift2 ; subst.
    remember (E2.Translation.phi) ; simpl in *|-*.
    inversion H1 ; subst.
    rewrite H5 ; inversion EqSsubstEq ; subst ; auto ~.
    assert((length t9) <= (length c1)).
    apply ContextStaticProperties.congr_context_ssubst_length in H7.
    destruct t10 ; simpl in *|-*.
    inversion H6 ; subst ; omega.
    inversion H6 ; subst.
    rewrite app_length in H7 ; omega.
    apply admin_context_ssubst_m_ge with (m:=length t9) ; auto ~.
    apply eq_context_ssubst_admin ; auto ~.
    (* End of duplicata *)

    rewrite H3, H6 ; auto ~.
    constructor ; auto ~.
  
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    rewrite <- app_comm_cons in H0.
    rewrite map_iter_stack_cs, map_iter_stack_bs in H0.
    remember (E2.Translation.phi) ; inversion H0 ; subst ; simpl in *|-* ; auto ~.
    apply app_cons_not_nil in H12 ; contradiction.
    destruct (Context.shift t9) ; destruct t9 ; inversion Shift2 ; subst.
    simpl in *|-* ; clear Shift2.
    assert(length c1 = length t9 + length c1'0)%nat.
    rewrite ContextStaticProperties.unshift_spec in H3.
    apply ContextStaticProperties.congr_context_ssubst_length in H7.
    rewrite H7.
    inversion H4 ; subst.
    rewrite app_length.
    inversion H15 ; subst.
    apply ContextStaticProperties.congr_context_ssubst_length in H13 ; rewrite H13 ; omega.
    apply ContextStaticProperties.congr_context_ssubst_length in H14 ; rewrite H14 ; omega.
    apply admin_context_ssubst_sum with (m1:=length c1'0) (b1:=(n0 + (length t9))%nat) ;
    auto ~ ; try(omega).

    simpl in Shift2 ; destruct (Context.shift t9) ; 
    destruct t9 ; inversion Shift2 ; subst.
    remember (E2.Translation.phi) ; simpl in *|-*.
    inversion H1 ; subst.
    rewrite H6 ; inversion EqSsubstEq ; subst ; auto ~.
    assert((length t9) <= (length c1)).
    apply ContextStaticProperties.congr_context_ssubst_length in H7.
    destruct t10 ; simpl in *|-*.
    inversion H4 ; subst ; omega.
    inversion H4 ; subst.
    rewrite app_length in H7 ; omega.
    apply admin_context_ssubst_m_ge with (m:=length t9) ; auto ~.
    apply eq_context_ssubst_admin ; auto ~.

    rewrite H3, H4 ; auto ~.

    (* length t7 <= length t5 *)
    specialize (ContextStaticProperties.shift_length t ) ; intros P3.
    rewrite <- Shift1 in P3.
    specialize (ContextStaticProperties.shift_length t0) ; intros P4.
    rewrite <- Shift2 in P4.
    rewrite H1, P3, P4 in *|-* ; auto ~.
  Qed.

  Lemma admin_stack_ssubst_merge_2:
    forall (bs:list nat) (dg1 dg2:dg_t) (dgs1 dgs2:list dg_t) (e1 e2 e3:S.expr), 
    let (e1', cs1) := trans e1 (map_iter_booker e2 bs 0) dg1 dgs1 in
    let (e2', cs2) := trans e2 bs dg2 dgs2 in
    let (e3', cs3) := trans e3 (map_iter_booker e2 bs 0) dg1 dgs1 in
    match cs1 with
    | nil => True
    | _ => let (c1, cs1') := Context.shift cs1 in
      match c1 with
      | nil => True
      | cons (t_eh, h) c1' => 
        forall (eh:S.expr),
        t_eh = trans_expr eh (0::nil) dg_empty nil ->
        match c1' with
        | nil =>
            admin_stack_ssubst (pred (depth e1)) h (phi eh (0 :: nil) dg_empty nil)
            (tl (map_iter_booker e2 bs 0))
            (hd 0 (map_iter_booker e2 bs 0)) cs1' cs3
        | _ :: _ =>
            admin_stack_ssubst (pred (depth e1)) h (phi eh (0 :: nil) dg_empty nil)
            (tl (map_iter_booker e2 bs 0))
            (hd 0 (map_iter_booker e2 bs 0)) (Context.unshift cs1' c1') cs3
        end ->
        depth e2 < depth e1 < length bs ->
        match c1' with
        | nil =>
          admin_stack_ssubst (pred (depth e1)) h (phi eh (0 :: nil) dg_empty nil) (tl bs)
          (hd 0 bs) (Context.merge cs1' cs2)
          (Context.merge cs3 cs2)
        | _ =>
          admin_stack_ssubst (pred (depth e1)) h (phi eh (0 :: nil) dg_empty nil) (tl bs)
          (hd 0 bs)
          (Context.unshift (Context.merge cs1' cs2) c1')
          (Context.merge cs3 cs2)
        end
      end
    end.
  Proof.
    intros.
    specialize (map_iter_booker_stack e2 bs dg2 dgs2) ; intros MapIterBooker.
    specialize (depth_length e1 (map_iter_booker e2 bs 0) dg1 dgs1) ; intros DpthLength1.
    specialize (depth_length e2 bs dg2 dgs2) ; intros DpthLength2.
    specialize (eq_ssubst_gt e2 bs dg2 dgs2) ; intros EqSsubstEq.
    destruct (trans e1).
    destruct (trans e2).
    destruct (trans e3).
    destruct t ; auto ~.
    cases (Context.shift (t :: t2)) as t eqn:Shift1.
    destruct t3 ; (* rewrite_eq E2.Translation.phi phi ; *) auto ~.
    destruct p ; intros.
    specialize (EqSsubstEq v (phi eh (0 :: nil) dg_empty nil) (depth e1) H1).
    destruct EqSsubstEq ; clear H2 ; destruct H3 ; clear H3.
    rewrite DpthLength1, DpthLength2, MapIterBooker in *|-*.
    clear H DpthLength1 DpthLength2 MapIterBooker.
    simpl in *|-*.
    destruct bs ; [exfalso ; simpl in *|-* ; omega |].
    rewrite map_iter_stack_bs in *|-*.
    simpl in *|-*.

    destruct t3.

    (* c1' nil *)
    clear Shift1.
    generalize dependent n ;
    generalize dependent t2 ; generalize dependent t1 ; 
    generalize dependent bs ; generalize dependent t0.
    induction t4 ; simpl in *|-* ; intros.
    inversion H0 ; subst.
    apply eq_stack_ssubst_admin ; auto ~.
    destruct t1.
    inversion H0 ; subst.
    simpl in *|-*.
    destruct bs ; [exfalso ; simpl in *|-* ; omega |].

    destruct t0 ; auto ~.
    rewrite map_iter_stack_nil in *|-* ; auto ~.
    simpl in *|-* ; rewrite plus_0_r in *|-* ; auto ~.

    (* induction case *)
    destruct t2 ; simpl in *|-* ; [exfalso ; omega|].
    assert(admin_stack_ssubst (length t6) v (phi eh (0 :: nil) dg_empty nil) bs n0
         (Context.merge t4 t5) (Context.merge t3 t5)).
    apply IHt4 ; auto ~ ; clear IHt4.
    omega.
    inversion H2 ; subst ; auto ~.
    constructor.

    rewrite map_iter_stack_bs, map_iter_stack_cs in H0 ; auto ~.
    inversion H0 ; subst ; auto ~.
    constructor.

    destruct t4.
    inversion H0 ; subst ; simpl in *|-* ; auto ~.
    destruct t5.
    constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    rewrite plus_0_r in H6 ; auto ~.
    apply eq_context_ssubst_admin ; auto ~.
    inversion H2 ; subst ; auto ~.
    
    constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    apply admin_context_ssubst_sum with (m1:=0) (b1:=(n0 + length t3)%nat) ;
    simpl in *|-* ; auto ~ ; omega.
    apply eq_context_ssubst_admin ; auto ~.
    inversion H2 ; subst ; auto ~.
    
    remember (Context.merge (t4 :: t7) t5).
    destruct t8.
    simpl in Heqt8 ; destruct t5 ; inversion Heqt8.
    remember (Context.merge t3 t5).
    destruct t10.
    inversion H0 ; subst.
    simpl in Heqt10 ; destruct t5 ; inversion Heqt10.
    destruct t5 ; auto ~.

    rewrite ContextStaticProperties.merge_nil_r in *|-*.
    simpl in *|-* ; inversion Heqt8 ; subst ; simpl in *|-*.
    constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    inversion H0 ; subst.
    rewrite plus_0_r in H7 ; auto ~.
    apply admin_context_ssubst_m_ge with (m:=0) ; auto ~ ; try(omega).
    apply eq_context_ssubst_admin ; auto ~.
    inversion H2 ; subst ; auto ~.
    
    constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    inversion H0 ; subst.
    clear H12 H0.
    apply admin_context_ssubst_sum with (m1:=length t4) (b1:=(n0 + (length t5))%nat) ;
    auto ~.
    simpl in Heqt8 ; inversion Heqt8 ; rewrite app_length ; omega.
    apply admin_context_ssubst_m_ge with (m:=length t5) ; auto ~ ; try(omega).
    apply eq_context_ssubst_admin ; auto ~.
    inversion H2 ; subst ; auto ~.
    simpl in Heqt8 ; inversion Heqt8 ; rewrite app_length ; omega.

    (* c1' not nil *)
    rewrite ContextStaticProperties.merge_unshift_1 ; auto ~.
    clear Shift1.
    rewrite ContextStaticProperties.unshift_spec in *|-*.
    generalize dependent n ;
    generalize dependent t2 ; generalize dependent t1 ; 
    generalize dependent bs ; generalize dependent t0.
    induction t4 ; simpl in *|-* ; intros.
    inversion H0 ; subst.
    destruct t0 ; auto ~.

    rewrite map_iter_stack_nil in *|-* ; subst ; auto ~.
    simpl in *|-* ; rewrite plus_0_r in *|-* ; auto ~.

    simpl in *|-*.
    rewrite map_iter_stack_cs in *|-*.
    inversion H2 ; subst.
    simpl in *|-*.
    constructor ; auto ~.
    rewrite map_iter_stack_nil in *|-* ; subst ; auto ~.
    inversion H ; subst ; auto ~.
    rewrite app_comm_cons.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    apply eq_context_ssubst_admin ; auto ~.
    constructor ; auto ~.
    rewrite map_iter_stack_bs, map_iter_stack_cs in *|-*.
    inversion H ; subst ; auto ~.
    rewrite app_comm_cons.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    apply admin_context_ssubst_sum with (m1:=0) (b1:=(b0 + length c1')%nat) ;
    auto ~ ; try(omega).
    apply eq_context_ssubst_admin ; auto ~.
    apply eq_stack_ssubst_admin ; auto ~.

    destruct bs ; [exfalso ; simpl in *|-* ; omega |].
    destruct t0 ; auto ~.
    rewrite map_iter_stack_nil in *|-* ; auto ~.
    simpl in *|-* ; rewrite plus_0_r in *|-* ; auto ~.
    rewrite ContextStaticProperties.merge_nil_r ; auto ~.
    rewrite map_iter_stack_bs, map_iter_stack_cs in *|-*.
    inversion H0 ; subst.
    apply app_cons_not_nil in H7 ; contradiction.

    (* induction case *)
    destruct t2 ; [simpl in *|-* ; exfalso ; omega|].
    assert(admin_stack_ssubst (length t2) v (phi eh (0 :: nil) dg_empty nil) bs n0
         (Context.merge (t4 ++ (p :: t3) :: nil) t5) (Context.merge (c2' :: cs2) t5)).
    apply IHt4 ; auto ~ ; clear IHt4 ; simpl in *|-*.
    omega.
    inversion H2 ; subst ; auto ~.
    constructor.
    rewrite <- H7 ; auto ~.

    remember (MP.Translation.Context.merge (c1' :: cs1) t5).
    destruct t6.
    simpl in Heqt6 ; destruct t5 ; inversion Heqt6.
    remember (Context.merge (c2' :: cs2) t5).
    destruct t8.
    simpl in Heqt8 ; destruct t5 ; inversion Heqt8.
    remember (c2' :: cs2) ; simpl ; subst.
    rewrite <- Heqt8.
    constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    simpl; auto ~.
    apply admin_context_ssubst_sum with (m1:=length c1') (b1:=(n0 + (length (nth 0 t5 nil)))%nat) ;
    auto ~.
    destruct t5 ; inversion Heqt6 ; subst ; 
    try(rewrite app_length) ; simpl ; omega.
    apply admin_context_ssubst_m_ge with (m:=(length (nth 0 t5 nil))) ; auto ~ ; try(omega).
    apply eq_context_ssubst_admin ; auto ~.
    inversion H2 ; subst ; auto ~.
    destruct t5 ; [simpl in *|-* ; omega|] ; inversion Heqt6 ; subst ; 
    simpl in *|-*.
    rewrite app_length ; omega.
    rewrite Heqt6, Heqt8, H7 in *|-* ; auto ~.

    (* length t0 <= length t4 *)
    specialize (ContextStaticProperties.shift_spec (t :: t2)) ; intros Spec1.
    simpl in Spec1.
    destruct (Context.shift t2).
    destruct t2 ; simpl in *|-* ; inversion Shift1 ; subst.
    destruct t0 ; [|exfalso] ; simpl in *|-* ; omega.
    assert(length (t :: t2 :: t7) = length ((t :: t6) ++ ((e5, v) :: p :: t3) :: nil)) as Eq1.
    rewrite Spec1 ; simpl ; auto ~ ; omega.
    simpl in Eq1.
    rewrite app_length in Eq1.
    simpl in *|-* ;
    rewrite <- plus_Snm_nSm, plus_0_r in Eq1.
    inversion Eq1 ; subst ; rewrite H3 in *|-*.
    destruct H1 ; generalize H ; clear ; intros.
    apply le_S_n in H ; auto ~.
  Qed.

  Lemma admin_stack_ssubst_merge_3:
    forall (bs:list nat) (dg1 dg2:dg_t) (dgs1 dgs2:list dg_t) (e1 e2 e3:S.expr), 
    let (e1', cs1) := trans e1 (map_iter_booker e2 bs 0) dg1 dgs1 in
    let (e2', cs2) := trans e2 bs dg2 dgs2 in
    let (e3', cs3) := trans e3 bs dg2 dgs2 in
    match cs2 with
    | nil => True
    | _ => let (c2, cs2') := Context.shift cs2 in
      match c2 with
      | nil => True
      | cons (t_eh, h) c2' => 
        forall (eh:S.expr),
        t_eh = trans_expr eh (0::nil) dg_empty nil ->
        match c2' with
        | nil =>
            admin_stack_ssubst (pred (depth e2)) h (phi eh (0 :: nil) dg_empty nil)
            (tl bs)
            (hd 0 bs) cs2' cs3
        | _ :: _ =>
            admin_stack_ssubst (pred (depth e2)) h (phi eh (0 :: nil) dg_empty nil)
            (tl bs)
            (hd 0 bs) (Context.unshift cs2' c2') cs3
        end ->
        depth e1 < depth e2 < length bs ->
        match c2' with
        | nil =>
          admin_stack_ssubst (pred (depth e2)) h (phi eh (0 :: nil) dg_empty nil) (tl bs)
          (hd 0 bs) (Context.merge cs1 cs2')
          (Context.merge cs1 cs3)
        | _ =>
          admin_stack_ssubst (pred (depth e2)) h (phi eh (0 :: nil) dg_empty nil) (tl bs)
          (hd 0 bs)
          (Context.unshift (Context.merge cs1 cs2') c2')
          (Context.merge cs1 cs3)
        end
      end
    end.
  Proof.
    intros.
    specialize (map_iter_booker_stack e2 bs dg2 dgs2) ; intros MapIterBooker.
    specialize (depth_length e1 (map_iter_booker e2 bs 0) dg1 dgs1) ; intros DpthLength1.
    specialize (depth_length e2 bs dg2 dgs2) ; intros DpthLength2.
    specialize (eq_ssubst_3_gt e1 (map_iter_booker e2 bs 0) dg1 dgs1) ; intros EqSsubstEq.
    specialize (StaticProperties.length_h_match e2 bs dg2 dgs2) ; intros LengthHMatch.
    destruct (trans e1).
    destruct (trans e2).
    destruct (trans e3).
    destruct t0 ; auto ~.
    cases (Context.shift (t0 :: t2)) as t eqn:Shift1.
    destruct t3 ; auto ~.
    destruct p ; intros.
    assert(length (t0 :: t2) <= length bs) as Tmp1.
    simpl in *|-* ; omega.
    specialize (LengthHMatch Tmp1) ; clear Tmp1.
    simpl in LengthHMatch.
    rewrite map_iter_booker_length in *|-*.
    specialize (EqSsubstEq v (phi eh (0 :: nil) dg_empty nil) (depth e2) H1).
    destruct EqSsubstEq ; clear H2 ; destruct H3 ; clear H3.
    rewrite DpthLength1, DpthLength2, MapIterBooker in *|-*.
    clear H DpthLength1 DpthLength2 MapIterBooker.
    simpl in *|-*.
    destruct bs ; [exfalso ; simpl in *|-* ; omega |].
    rewrite map_iter_stack_bs in *|-*.
    simpl in *|-*.

    destruct t3.
    

    (* c2' nil *)
    
    generalize dependent n ;
    generalize dependent t ;
    generalize dependent t2 ; generalize dependent t1 ; 
    generalize dependent bs ; generalize dependent t0.
    induction t4 ; simpl ; intros.
    inversion H0 ; subst.
    repeat(rewrite ContextStaticProperties.merge_nil_r).
    apply eq_stack_ssubst_3_admin ; auto ~.
    rewrite map_iter_stack_cs in H2.
    destruct (Context.shift t2).
    destruct t2 ; inversion Shift1 ; subst.
    destruct t ; simpl in *|-* ; [|exfalso ; omega] ; constructor.

    (* induction case *)
    destruct t1 ; [inversion H0|].
    destruct t ; auto ~.
    rewrite map_iter_stack_cs in *|-*.
    destruct bs ; [simpl in *|-* ; exfalso ; omega|].
    destruct t2 ; [simpl in *|-* ; exfalso ; omega|].
    assert(admin_stack_ssubst (length t6) v (phi eh (0 :: nil) dg_empty nil) bs n0
         (Context.merge t5 t4) (Context.merge t5 t3)).
    simpl in Shift1.
    apply IHt4 with (t0:=t2) ; auto ~ ; try(simpl in *|-* ; omega).
    destruct (Context.shift t6) ; destruct t6 ; inversion Shift1 ; substs ; auto ~.
    simpl in *|-* ; inversion H2 ; subst ; auto ~ ; constructor.
    inversion H0 ; subst ; auto ~ ; constructor.
    clear IHt4.

    simpl.
    remember (Context.merge t5 t4).
    destruct t7.
    apply ContextStaticProperties.merge_nil in Heqt7 ; destruct Heqt7 ; subst.
    simpl in *|-* ; inversion H ; subst ; simpl in *|-*.

    (* Duplication part *)
    constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    inversion H2 ; subst ; auto ~.
    destruct (Context.shift t6).
    destruct t6 ; inversion Shift1 ; subst.
    apply eq_context_ssubst_3_admin ; auto ~.
    simpl in *|-*.
    apply eq_context_ssubst_3_h_lt with (b1:=(n0+1)%nat) (m1:=0) ; auto ~ ; omega.
    inversion H0 ; subst ; auto ~.
    (* End duplication *)

    remember (Context.merge t5 t3) ; destruct t9.
    inversion H ; subst.

    constructor ; auto ~.

    (* Duplication part *)
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    rewrite map_iter_stack_bs, map_iter_stack_cs in H2 ; auto ~.
    assert(a = t0) as Eq1 ; [|rewrite Eq1 in *|-* ; clear Eq1].
    simpl in Shift1 ;
    destruct (Context.shift t6) ; destruct t6 ; inverts Shift1 ; auto ~.
    inverts H2 ; auto ~.
    assert(length t2 = length t7) as Eq2.
    simpl in Heqt7, Shift1 ; inverts Heqt7 ;
    destruct (Context.shift t6) ; destruct t6 ; inverts Shift1 ; auto ~.
    apply admin_context_ssubst_sum with (m1:=0) (b1:=(n0 + length t7)%nat) ;
    rewrite Eq2 in *|-* ; auto ~ ; apply eq_context_ssubst_3_admin ; simpl in *|-* ; auto ~.
    simpl in LengthHMatch.
    simpl in *|-* ; destruct (Context.shift t6) ; destruct t6 ; inverts Shift1.
    apply eq_context_ssubst_3_admin ; auto ~.
    simpl in *|-*.
    inverts Heqt7.
    rewrite StaticProperties.map_iter_stack_nil in*|-*.
    apply eq_context_ssubst_3_h_lt with (b1:=(n0+1)%nat) (m1:=0) ; auto ~ ; omega.
    assert((length c1' + length t2)%nat = length t7) as Eq2.
    inverts Heqt7 ; rewrite app_length ; omega.
    apply admin_context_ssubst_sum with (m1:=length c1') (b1:=(n0 + length t2)%nat) ; 
    auto ~ ; try(omega).
    apply eq_context_ssubst_3_admin ; auto ~.
    (* end duplication *)
    
    inverts H0 ; auto ~.
    apply admin_context_ssubst_m_ge with (m:=0) ; auto ~ ; omega.
    apply admin_context_ssubst_m_ge with (m:=length c1') ; auto ~.
    destruct t5 ; simpl in Heqt7 ; inverts Heqt7 ; try(rewrite app_length) ; omega.

    (* c2' not nil *)
    rewrite ContextStaticProperties.merge_unshift_2 ; auto ~.

    generalize dependent n ;
    generalize dependent t ;
    generalize dependent t2 ; generalize dependent t1 ; 
    generalize dependent t3 ; 
    generalize dependent bs ; generalize dependent t0.
    induction t4 ; simpl ; intros.
    inverts H0.
    rewrite map_iter_stack_cs in *|-*.
    destruct (Context.shift t2).
    destruct t2 ; inverts Shift1.
    destruct t ; simpl in *|-* ; [|exfalso ; omega] ; constructor ; auto ~.

    destruct t.
    simpl in *|-* ; auto ~.

    (* induction case *)
    destruct t2 ; [simpl in *|-* ; exfalso ; omega|].
    destruct t1.
    inversion H0.
    destruct bs ; [exfalso ; simpl in *|-* ; omega |].
    simpl.
    assert(admin_stack_ssubst (length t6) v (phi eh (0 :: nil) dg_empty nil) bs n0
         (Context.merge t5 (Context.unshift t4 (p::t3))) (Context.merge t5 t7)).
    apply IHt4 with (t0:=t2) ; auto ~ ; try(simpl in *|-* ; omega).
    simpl in *|-* ; destruct (Context.shift t6) ; destruct t6 ; inversion Shift1 ; substs ; auto ~.
    rewrite map_iter_stack_bs, map_iter_stack_cs in *|-*.
    rewrite map_iter_stack_cs in *|-*.
    inversion H2 ; subst ; auto ~ ; constructor.
    inversion H0 ; subst ; auto ~ ; constructor.
    clear IHt4.

    remember ((MP.Translation.Context.merge t5 
      (MP.Translation.Context.unshift t4 (p :: t3)))).
    destruct t8.
    apply ContextStaticProperties.merge_nil in Heqt8.
    destruct Heqt8.
    rewrite ContextStaticProperties.unshift_spec in H4.
    destruct t4 ; simpl in H4 ; inversion H4.
    
    remember (Context.merge t5 t7).
    destruct t10.
    inverts H.

    constructor ; auto ~.
    apply ContextStaticProperties.congr_ssubst_context_app ; auto ~.
    rewrite map_iter_stack_bs, map_iter_stack_cs in H2 ; auto ~.
    assert(a = t0) as Eq1 ; [|rewrite Eq1 in *|-* ; clear Eq1].
    simpl in Shift1 ;
    destruct (Context.shift t6) ; destruct t6 ; inverts Shift1 ; auto ~.

    inverts H2 ; auto ~.
    simpl in *|-* ; destruct (Context.shift t6) ; destruct t6 ; inverts Shift1 ; auto ~.
    apply eq_context_ssubst_3_admin ; auto ~.
    apply eq_context_ssubst_3_h_lt with (b1:=(n0+length ((e5, v) :: p :: t3))%nat) (m1:=0) ; auto ~.
    rewrite LengthHMatch ; simpl ; omega.

    assert(length t2 = length t8) as Eq2.
    simpl in Heqt8 ; inverts Heqt8 ; simpl ; auto ~.
    apply admin_context_ssubst_sum with (m1:=0) (b1:=(n0 + length t8)%nat) ;
    rewrite Eq2 in *|-* ; auto ~ ; apply eq_context_ssubst_3_admin ; simpl in *|-* ; auto ~.
    
    simpl in *|-* ; destruct (Context.shift t6) ; destruct t6 ; inverts Shift1 ; auto ~.
    apply eq_context_ssubst_3_admin ; auto ~.
    apply eq_context_ssubst_3_h_lt with (b1:=(n0+length ((e5, v) :: p :: t3))%nat) (m1:=(length c1')) ; auto ~.
    rewrite LengthHMatch ; simpl ; omega.

    assert((length c1' + length t2)%nat = length t8) as Eq2.
    simpl in Heqt8 ; inverts Heqt8 ; simpl ; rewrite app_length ; auto ~.
    apply admin_context_ssubst_sum with (m1:=length c1') (b1:=(n0 + length t2)%nat).
    apply eq_context_ssubst_3_admin ; simpl in *|-* ; auto ~.
    omega.
    
    inverts H0 ; auto ~.
    apply admin_context_ssubst_m_ge with (m:=0) ; auto ~ ; omega.
    apply admin_context_ssubst_m_ge with (m:=length c1') ; auto ~.
    destruct t4 ; simpl in H8 ; inverts H8 ;
    destruct t5 ; simpl in Heqt8 ; inverts Heqt8 ; try(rewrite app_length) ; omega.
    
    (* length t0 <= length t4 *)
    specialize (ContextStaticProperties.shift_spec t2) ; intros Spec1.
    destruct (Context.shift t2).
    destruct t2.
    inversion Shift1 ; subst.
    omega.
    inversion Shift1 ; subst.
    clear Shift1 ; simpl in Spec1.
    assert(length (t2 :: t7) = S (length t6)) as Eq1.
    rewrite Spec1 ; try(omega).
    rewrite app_length ; simpl ; omega.
    simpl in *|-* ; rewrite <- Eq1.
    omega.
  Qed.

End AdminSubstProperties.
