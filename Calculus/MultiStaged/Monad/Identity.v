Require Import Coq.Arith.Arith.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import "Misc/Library".
Require Import "Calculus/Sets".
Require Import "Calculus/Definitions".
Require Import "Calculus/Monad".
Require Import "Calculus/MultiStaged/Definitions".
Require Import "Calculus/MultiStaged/Monad".

(** * Monad **)

(**
  Monadic translation with identity monad sends a calculus to itself.
  It is the simplest possible monad. We prove that identity monad
  verifies required algebraic properties.
*)

Module IdentityMonad (R:Replacement) (T:ReplacementCalculus R) <: (Monad R T).

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

  (** Substitution Properties *)
  Lemma ssubst_ret :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (ret e) v = ret (ssubst n ss (cast_var x) e v).
  Proof.
    reflexivity.
  Qed.

  Lemma ssubst_bind :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e1 v:expr) (e2: expr -> expr),
     ((fun v2 => ssubst n ss (cast_var x) (e2 v2) v) = 
       fun v2 => e2 (ssubst n ss (cast_var x) v2 v)) ->
     ssubst n ss (cast_var x) (bind e1 e2) v = 
       bind (ssubst n ss (cast_var x) e1 v) e2.
  Proof.
    intros.
    unfold bind.
    assert(forall v2, ((fun v2 : expr => ssubst n ss (cast_var x) (e2 v2) v) v2 =
     (fun v2 : expr => e2 (ssubst n ss (cast_var x) v2 v)) v2)).
      apply equal_f.
      assumption.
    specialize (H0 e1).
    simpl in H0.
    assumption.
  Qed.

(*  Parameter ssubst_bind_2 :
    forall (n:nat) (ss:StageSet.t) (x:var) (e1 v:expr) (e2: expr -> expr),
     ssubst n ss x (bind e1 e2) v = 
       bind e1 (fun v2 => e2 (ssubst n ss x v2 v)).*)

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
     cast_efix (cast_var f) (cast_var y) (ssubst n (if orb (S.beq_var x f) (S.beq_var x y) 
        then (StageSet.add n ss) else ss) (cast_var x) e v).
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

End IdentityMonad.
