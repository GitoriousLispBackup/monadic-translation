Require Import Coq.Arith.Arith.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import "Misc/Library".
Require Import "Calculus/Sets".
Require Import "Calculus/Definitions".
Require Import "Calculus/Monad".
Require Import "Calculus/MultiStaged/Definitions".
Require Import "Calculus/MultiStaged/Properties".
Require Import "Calculus/MultiStaged/Monad".

(** * Monad **)

(**
  Monadic translation with identity monad sends a calculus to itself.
  It is the simplest possible monad. We prove that identity monad
  verifies required algebraic properties.
*)

Module Type IdentityMonad (R:Replacement) (T:ReplacementCalculus R) <: (Monad R T).

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

  Definition ret (e:expr) : expr := e.
  Definition bind (e: expr) (f:expr -> expr) := f e.

  Definition ssubst : nat -> StageSet.t -> var -> expr -> expr -> expr := ssubst.
  Definition bv : nat -> expr -> VarSet.t := bv.

  (** Var Translation *)
  Definition cast_var (v:var) : var := v.

  (** Abstract Reduction step *)
  Definition astep : relation state := sstep 0.

End IdentityMonad.

Module Type IdentityMonadProperties (R:Replacement) 
  (T:ReplacementCalculus R) (M:IdentityMonad R T) <: MonadProperties R T M.

  Module Translation := Translation R T M.
  Module TSP := TranslationStaticProperties R T M.
  Module CalculusProperties := CalculusProperties R T.
  Import Translation.
  Import T.
  Import M.

  (** Substitution Properties *)
  Lemma ssubst_ret :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (ret e) v = 
	ret (ssubst n ss (cast_var x) e v).
  Proof.
    reflexivity.
  Qed.

  Lemma ssubst_bind :
    forall (n:nat) (ss:StageSet.t) (x:S.var) 
	(e1 v:expr) (f1 f2: expr -> expr),
     ((fun v2 => ssubst n ss (cast_var x) (f1 v2) v) = 
       fun v2 => f2 (ssubst n ss (cast_var x) v2 v)) ->
     ssubst n ss (cast_var x) (bind e1 f1) v = 
       bind (ssubst n ss (cast_var x) e1 v) f2.
  Proof.
    intros.
    unfold bind.
    assert(forall v2, ((fun v2 => ssubst n ss (cast_var x) (f1 v2) v) v2 =
     (fun v2 => f2 (ssubst n ss (cast_var x) v2 v)) v2)).
      apply equal_f.
      assumption.
    specialize (H0 e1).
    simpl in H0.
    assumption.
  Qed.

  Lemma ssubst_eabs :
    forall (n:nat) (ss:StageSet.t) (x y:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_eabs (cast_var y) e) v = 
     cast_eabs (cast_var y) (ssubst n (if S.beq_var x y 
        then (StageSet.add n ss) else ss) (cast_var x) e v).
  Proof.
    reflexivity.
  Qed.

  Lemma ssubst_efix :
    forall (n:nat) (ss:StageSet.t) (x f y:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_efix (cast_var f) (cast_var y) e) v = 
     cast_efix (cast_var f) (cast_var y) 
	(ssubst n (if orb (S.beq_var x f) (S.beq_var x y) 
        then (StageSet.add n ss) else ss) (cast_var x) e v).
  Proof.
    reflexivity.
  Qed.

  Lemma ssubst_eapp :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e1 e2 v:expr),
     ssubst n ss (cast_var x) (cast_eapp e1 e2) v
       = cast_eapp (ssubst n ss (cast_var x) e1 v) 
         (ssubst n ss (cast_var x) e2 v).
  Proof.
    reflexivity.
  Qed.

  Lemma ssubst_eref :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_eref e) v
       = cast_eref (ssubst n ss (cast_var x) e v).
  Proof.
    reflexivity.
  Qed.

  Lemma ssubst_deref :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_ederef e) v
       = cast_ederef (ssubst n ss (cast_var x) e v).
  Proof.
    reflexivity.
  Qed.

  Lemma ssubst_eassign :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e1 e2 v:expr),
     ssubst n ss (cast_var x) (cast_eassign e1 e2) v
       = cast_eassign (ssubst n ss (cast_var x) e1 v) 
         (ssubst n ss (cast_var x) e2 v).
  Proof.
    reflexivity.
  Qed.

  Lemma ssubst_ebox :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_ebox e) v
       = cast_ebox (ssubst (S n) ss (cast_var x) e v).
  Proof.
    reflexivity.
  Qed.


  (** Abstract Reduction Properties *)

(*  Lemma length_trans:
    forall (e:expr) (acc:Splitter.t),
    depth (trans_expr e acc) <= depth e.
  Proof.
    induction e ; simpl ; intros ;
    try(reflexivity) ;
    try(unfold trans_expr in *|-* ; simpl in *|-* ;
    specialize (IHe acc) ; destruct (trans e) ;
    rewrite IHe ; reflexivity) ;
    try(unfold trans_expr in *|-* ; simpl in *|-* ;
    specialize (IHe1 (Splitter.left acc)) ; 
    specialize (IHe2 (Splitter.right acc)) ;
    destruct (trans e1) ; destruct (trans e2) ;
    rewrite IHe1 ; rewrite IHe2 ;
    reflexivity).

    unfold trans_expr in *|-* ; simpl in *|-* ;
    specialize (IHe acc).
    destruct (trans e).
    rewrite IHe.
    destruct t.
    reflexivity.
    
  ; reflexivity.

  Qed.*)

(*
  Lemma length_svalue:
    forall (e:expr) (acc:Splitter.t) (n:nat),
    let (_, cs) := trans e acc in
    length cs < (S n) <-> svalue (S n) e.
  Proof.
    intros.
    specialize (depth_length e) ; intros.
    specialize (H acc).
    destruct (trans e).
    rewrite <- H.
    apply CalculusProperties.depth_svalue.
  Qed.*)

  Lemma phi_svalue:
    forall (e:expr) (acc:Splitter.t),
    S.svalue 0 e -> svalue 0 (phi e acc).
  Proof.
    intros ; inversion H ; subst ; simpl in *|-* ;
    try(constructor ; fail) ;
    try(destruct (trans e0) ; constructor ; fail).
    specialize (TSP.length_svalue e0 acc 0) ; intros.
    assert(TSP.Translation.trans = trans).
    reflexivity.
    rewrite H2 in H1.

    (* TODO: Prove it *)
    assert(depth (trans_expr e0 acc) = 0).
    admit.

    assert(depth (trans_expr e0 acc) < 1).
    rewrite H3.
    auto.

    apply CalculusProperties.depth_svalue in H4.
    unfold trans_expr in H4.
    destruct (trans e0).
    constructor ; assumption.
  Qed.

  Lemma astep_bind_1 :
    forall (e1 e2 ef:expr) (acc:Splitter.t) (M1 M2:Memory.t) (x:var),
    let f := fun v => cast_eapp (cast_eabs x ef) v in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind e1 f) (M2, bind e2 f).
  Proof.
    intros.
    unfold bind, f, cast_eapp, cast_eabs.
    constructor.
    constructor.
    assumption.
  Qed.

  Lemma astep_bind_2 :
    forall (v:S.expr) (e:expr) (acc:Splitter.t) (M1 M2:Memory.t) (f:expr -> expr),
    S.svalue 0 v -> astep (M1, (f (phi v acc))) (M2, e) ->
    astep (M1, (bind (ret (phi v acc)) f)) (M2, e).
  Proof.
    intros ; assumption.
  Qed.

  Lemma astep_app_abs :
    forall (v:S.expr) (x:S.var) (e:expr) (acc:Splitter.t) (M:Memory.t),
    S.svalue 0 v -> astep (M, cast_eapp
      (cast_eabs (cast_var x) e) (phi v acc))
      (M, ssubst 0 StageSet.empty (cast_var x) e (phi v acc)).
  Proof.
    intros.
    constructor.
    apply phi_svalue ; assumption.
  Qed.

End IdentityMonadProperties.
