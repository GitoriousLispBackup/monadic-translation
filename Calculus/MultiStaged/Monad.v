Require Import Coq.Relations.Relation_Definitions.
Require Import "Calculus/Sets".
Require Import "Calculus/Definitions".
Require Import "Calculus/Monad".
Require Import "Calculus/MultiStaged/Definitions".

(* Monad R T <: StagedMonad (Calculus R) T. *)
Module Type Monad (R:Replacement) (T:StagedCalculus).

  Module S := Calculus R.
  Import T.

  Parameter cast_econst: nat -> T.expr.
  Parameter cast_evar: T.var -> T.expr.
  Parameter cast_eabs: T.var -> T.expr -> T.expr.
  Parameter cast_efix: T.var -> T.var -> T.expr -> T.expr.
  Parameter cast_eapp: T.expr -> T.expr -> T.expr.
  Parameter cast_eloc: S.location -> T.expr.
  Parameter cast_eref: T.expr -> T.expr.
  Parameter cast_ederef: T.expr -> T.expr.
  Parameter cast_eassign: T.expr -> T.expr -> T.expr.
  Parameter cast_ebox: T.expr -> T.expr.
  Parameter cast_eunbox: T.expr -> T.expr.
  Parameter cast_erun: T.expr -> T.expr.
  Parameter cast_elift: T.expr -> T.expr.

  Parameter ret : T.expr -> T.expr.
  Parameter bind : T.expr -> (T.expr -> T.expr) -> T.expr.

  Parameter ssubst : nat -> StageSet.t -> var -> expr -> expr -> expr.
  Parameter bv : nat -> expr -> VarSet.t.

  (** Var Translation *)
  Parameter cast_var: S.var -> T.var.

  (** Abstract Reduction step *)
  Parameter astep : relation T.state.

End Monad.

