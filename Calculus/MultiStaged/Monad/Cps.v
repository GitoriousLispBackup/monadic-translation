Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import "Misc/Tactics".
Require Import "Misc/Library".
Require Import "Calculus/Sets".
Require Import "Calculus/Definitions".
Require Import "Calculus/Monad".
Require Import "Calculus/MultiStaged/Definitions".
Require Import "Calculus/MultiStaged/Properties".
Require Import "Calculus/MultiStaged/Monad".

(** * Monad **)

Module Type CpsMonad (R:Replacement) (T:ReplacementCalculus R) <: (Monad R T).

  Import T.CRaw.

  Module S := Calculus R.

  Definition cast_econst (i:nat) : expr := EConst i.
  Definition cast_evar (x:var) : expr := EVar x.
  Definition cast_eabs (x:var) (e:expr) : expr := EAbs x e.
  Definition cast_efix (f x:var) (e:expr) : expr := EFix f x e.
  Definition cast_eapp (e1 e2:expr) : expr := EApp e1 e2.
  Definition cast_eloc (l:location) : expr := ELoc l.
  Definition cast_eref (e:expr) : expr := ERef e.
  Definition cast_ederef (e:expr) : expr := EDeref e.
  Definition cast_eassign (e1 e2:expr) : expr := EAssign e1 e2.
  Definition cast_ebox (e:expr) : expr := EBox e.
  Definition cast_eunbox (e:expr) : expr := EUnbox e.
  Definition cast_erun (e:expr) : expr := ERun e.
  Definition cast_elift (e:expr) : expr := ELift e.

  Definition ret (e:expr) : expr := let v := (S (2*0))%nat in EAbs v (EApp (EVar v) e).
  Definition bind (e: expr) (f:expr -> expr) := 
    let v := (S (2*0))%nat in EAbs v (EApp e (f (EVar v))).

  Definition ssubst : nat -> StageSet.t -> var -> expr -> expr -> expr := ssubst.
  Definition bv : nat -> expr -> VarSet.t := bv.

  (** Var Translation *)
  Definition cast_var (v:var) : var := (2*v)%nat.

  (** Colon Translation *)
  Definition colon (k e:expr) := match e with
  | EAbs x e => ssubst 0 StageSet.empty x e k
  | _ => EApp e k
  end.

  (** Abstract Reduction step *)
  Definition astep : relation state := 
    fun s1 s2 => let (M1,e1) := s1 in
    let (M2,e2) := s2 in
    forall k, clos_trans state (sstep 0) (M1, colon k e1) (M2, colon k e2).

End CpsMonad.

Module Type CpsMonadProperties (R:Replacement) 
  (T:ReplacementCalculus R) (M:CpsMonad R T) <: MonadProperties R T M.

  Module Translation := Translation R T M.
  Module BindingSetProperties := BindingSetProperties R.
  Import Translation.
  Import T.
  Import M.

  (** Custom Properties *)

  Lemma cast_var_disjoint:
    forall (m n:nat),
    beq_nat (cast_var m) (S (n + (n + 0))) = false.
  Proof.
    intros ; apply beq_nat_false_iff.
    unfold cast_var ; omega.
  Qed.

  Lemma cast_var_injective:
    forall (m n:nat),
    m <> n -> cast_var m <> cast_var n.
  Proof.
    intros ; unfold cast_var ; omega.
  Qed.

  (** Substitution Properties *)

  Lemma ssubst_ret :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (ret e) v = ret (ssubst n ss (cast_var x) e v).
  Proof.
    intros ; unfold ret ; simpl ;
    specialize (cast_var_disjoint x 0) ; intros ;
    simpl in H ; rewrite H ; simpl ; auto.
  Qed.

  Lemma ssubst_bind :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e1 v:expr) (f1 f2: expr -> expr),
     (forall v2, (ssubst n ss (cast_var x) (f1 v2) v) = 
       f2 (ssubst n ss (cast_var x) v2 v)) ->
     ssubst n ss (cast_var x) (bind e1 f1) v = 
       bind (ssubst n ss (cast_var x) e1 v) f2.
  Proof.
    intros ; unfold ret ; simpl ;
    specialize (cast_var_disjoint x 0) ; intros ;
    simpl in H0 ; rewrite H0 ; simpl ; auto.
    unfold bind ; simpl.
    rewrite H.
    simpl.
    rewrite H0 ; auto.
  Qed.

  Lemma ssubst_econst :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (c:nat) (v:expr),
     ssubst n ss (cast_var x) (cast_econst c) v = cast_econst c.
  Proof.
    intros ; reflexivity.
  Qed.

  Lemma ssubst_evar :
    forall (n:nat) (ss:StageSet.t) (x y:S.var) (v:expr),
     ssubst n ss (cast_var x) (cast_evar (cast_var y)) v = 
     if beq_nat x y && S.CRaw.BindingSet.rho n ss 
     then v else (cast_evar (cast_var y)).
  Proof.
    intros ; simpl.
    case_beq_nat x y ; simpl ; auto.
    rewrite <- beq_nat_refl ; auto.
    apply cast_var_injective in E.
    apply beq_nat_false_iff in E ; rewrite E ; auto.
  Qed.

  Lemma ssubst_eabs :
    forall (n:nat) (ss:StageSet.t) (x y:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_eabs (cast_var y) e) v = 
     cast_eabs (cast_var y) (ssubst n (if S.beq_var x y 
        then (StageSet.add n ss) else ss) (cast_var x) e v).
  Proof.
    intros ; simpl ; unfold S.beq_var.
    case_beq_nat x y ; simpl ; auto.
    rewrite <- beq_nat_refl ; auto.
    apply cast_var_injective in E.
    apply beq_nat_false_iff in E ; rewrite E ; auto.
  Qed.

  Lemma ssubst_efix :
    forall (n:nat) (ss:StageSet.t) (x f y:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_efix (cast_var f) (cast_var y) e) v = 
     cast_efix (cast_var f) (cast_var y) (ssubst n (if orb (S.beq_var x f) (S.beq_var x y) 
        then (StageSet.add n ss) else ss) (cast_var x) e v).
  Proof.
    intros ; simpl ; unfold S.beq_var.
    case_beq_nat x f ; simpl ; auto.
    rewrite <- beq_nat_refl ; auto.
    case_beq_nat x y ; simpl ; auto.
    rewrite <- beq_nat_refl ; auto.
    rewrite orb_true_r ; auto.
    apply cast_var_injective in E.
    apply cast_var_injective in E0.
    apply beq_nat_false_iff in E.
    apply beq_nat_false_iff in E0.
    rewrite E, E0 ; auto.
  Qed.

  Lemma ssubst_eapp :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e1 e2 v:expr),
     ssubst n ss (cast_var x) (cast_eapp e1 e2) v
       = cast_eapp (ssubst n ss (cast_var x) e1 v) 
         (ssubst n ss (cast_var x) e2 v).
  Proof.
    intros ; reflexivity.
  Qed.

  Lemma ssubst_eloc :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (l:nat) (v:expr),
     ssubst n ss (cast_var x) (cast_eloc l) v = cast_eloc l.
  Proof.
    intros ; reflexivity.
  Qed.

  Lemma ssubst_eref :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_eref e) v
       = cast_eref (ssubst n ss (cast_var x) e v).
  Proof.
    intros ; reflexivity.
  Qed.

  Lemma ssubst_ederef :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_ederef e) v
       = cast_ederef (ssubst n ss (cast_var x) e v).
  Proof.
    intros ; reflexivity.
  Qed.

  Lemma ssubst_eassign :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e1 e2 v:expr),
     ssubst n ss (cast_var x) (cast_eassign e1 e2) v
       = cast_eassign (ssubst n ss (cast_var x) e1 v) 
         (ssubst n ss (cast_var x) e2 v).
  Proof.
    intros ; reflexivity.
  Qed.

  Lemma ssubst_ebox :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_ebox e) v
       = cast_ebox (ssubst (S n) ss (cast_var x) e v).
  Proof.
    intros ; reflexivity.
  Qed.

  Lemma ssubst_eunbox :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_eunbox e) v
       = cast_eunbox (ssubst (pred n) (StageSet.remove n ss) (cast_var x) e v).
  Proof.
    intros ; reflexivity.
  Qed.

  Lemma ssubst_erun :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_erun e) v
       = cast_erun (ssubst n ss (cast_var x) e v).
  Proof.
    intros ; reflexivity.
  Qed.

  Lemma ssubst_elift :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_elift e) v
       = cast_elift (ssubst n ss (cast_var x) e v).
  Proof.
    intros ; reflexivity.
  Qed.

  (** Abstract Reduction Properties *)

  Lemma astep_bind_app :
    forall (e1 e2 ef:expr) (M1 M2:Memory.t),
    let f := fun v1 => bind ef (fun v2 : T.expr => cast_eapp v1 v2) in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind e1 f) (M2, bind e2 f).
  Proof.
    intros ; unfold f, bind in *|-* ; simpl in *|-* ; intros.
    simpl ; specialize (H k) ; clear f.
    apply clos_trans_t1n_iff in H ; apply clos_trans_t1n_iff.
    admit. (* todo: prove it *)
  Qed.

  Parameter astep_bind_app_svalue :
    forall (v:S.expr) (e1 e2:expr) (M1 M2:Memory.t) (bs:list nat),
    S.svalue 0 v ->
    let f := fun v1 => cast_eapp (phi v bs) v1 in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind e1 f) (M2, bind e2 f).

  Parameter astep_bind_app_eabs :
    forall (e1 e2 ef:expr) (M1 M2:Memory.t) (x:var),
    let f := fun v => cast_eapp (cast_eabs x ef) v in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind e1 f) (M2, bind e2 f).

  Parameter astep_bind_app_efix :
    forall (e1 e2 ef:expr) (M1 M2:Memory.t) (f x:var),
    let f := fun v => cast_eapp (cast_efix f x ef) v in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind e1 f) (M2, bind e2 f).

  Parameter astep_bind_eref :
    forall (e1 e2:expr) (M1 M2:Memory.t),
    let f := fun v => cast_eref v in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind e1 f) (M2, bind e2 f).

  Parameter astep_bind_ederef :
    forall (e1 e2:expr) (M1 M2:Memory.t),
    let f := fun v => cast_ederef v in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind e1 f) (M2, bind e2 f).

  Parameter astep_bind_assign :
    forall (e1 e2 ef:expr) (M1 M2:Memory.t),
    let f := fun v1 => bind ef (fun v2 : T.expr => cast_eassign v1 v2) in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind e1 f) (M2, bind e2 f).

  Parameter astep_bind_erun :
    forall (e1 e2:expr) (M1 M2:Memory.t),
    let f := fun v => cast_erun v in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind e1 f) (M2, bind e2 f).

  Parameter astep_bind_elift :
    forall (e1 e2:expr) (M1 M2:Memory.t),
    let f := fun v => cast_elift v in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind e1 f) (M2, bind e2 f).

  Parameter astep_bind_1 :
    forall (v:S.expr) (e1 e2:expr) (bs:list nat) (M1 M2:Memory.t) (f:expr -> expr),
    S.svalue 0 v -> astep (M1, e1) (M2, e2) ->
    admin e2 (ret (phi v bs)) ->
    astep (M1, (bind e1 f)) (M2, (f (phi v bs))).

  Parameter astep_bind_2 :
    forall (v:S.expr) (e:expr) (bs:list nat) (M1 M2:Memory.t) (f:expr -> expr),
    S.svalue 0 v -> astep (M1, (f (phi v bs))) (M2, e) ->
    astep (M1, (bind (ret (phi v bs)) f)) (M2, e).

  Parameter astep_app_abs :
    forall (v:S.expr) (x:S.var) (e:expr) (bs:list nat) (M:Memory.t),
    S.svalue 0 v -> astep (M, cast_eapp
      (cast_eabs (cast_var x) e) (phi v bs))
      (M, ssubst 0 StageSet.empty (cast_var x) e (phi v bs)).

  Parameter astep_app_fix :
    forall (v:S.expr) (f x:S.var) (e:expr) (bs:list nat) (M:Memory.t),
    S.svalue 0 v -> astep (M, cast_eapp
      (cast_efix (cast_var f) (cast_var x) e) (phi v bs))
      (M, ssubst 0 StageSet.empty (cast_var f)
      (ssubst 0 StageSet.empty (cast_var x) e (phi v bs))
      (cast_efix (cast_var f) (cast_var x) e)).

  Parameter astep_eref :
    forall (v:S.expr) (M:Memory.t) (bs:list nat),
    S.svalue 0 v -> 
    astep (M, cast_eref (phi v bs))
    (Memory.set (Memory.fresh M) (phi v bs) M,
      ret (cast_eloc (Memory.fresh M))).
    
  Parameter astep_ederef :
    forall (l:S.location) (M:Memory.t) (bs:list nat),
    l < length M ->
    astep (M, cast_ederef (cast_eloc l)) (M, ret (Memory.get l M)).

  Parameter astep_erun :
    forall (M:Memory.t) (e:S.expr) (bs:list nat),
    S.svalue 1 e ->
    astep (M, cast_erun (cast_ebox (trans_expr e bs))) (M, trans_expr e bs).

  Lemma astep_elift :
    forall (M:Memory.t) (e:S.expr) (bs:list nat),
    S.svalue 0 e ->
    astep (M, cast_elift (phi e bs)) (M, ret (cast_ebox (ret (phi e bs)))).
  Proof.
    intros.
    unfold astep ; intros.
    unfold cast_elift.
    unfold cast_ebox.
    unfold colon.
    simpl.
    rewrite BindingSetProperties.rho_O_true.
  Qed.

End CpsMonadProperties.
