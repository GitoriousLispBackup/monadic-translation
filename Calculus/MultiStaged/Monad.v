Require Import Coq.Relations.Relation_Definitions.
Require Import "Calculus/Sets".
Require Import "Calculus/Definitions".
Require Import "Calculus/Monad".
Require Import "Calculus/MultiStaged/Definitions".

Module Type Monad (R:Replacement) 
  (S:ReplacementCalculus R) (T:StagedCalculus)
  <: StagedMonad S T.

  Import T.

  (** Data Gathering *)
  Parameter dg_t: Type.
  Parameter dg_empty: dg_t.
  Parameter dg_eabs: dg_t -> S.var -> dg_t.
  Parameter dg_efix: dg_t -> S.var -> S.var -> dg_t.
  Parameter dg_eapp_l: dg_t -> dg_t.
  Parameter dg_eapp_r: dg_t -> dg_t.
  Parameter dg_eref: dg_t -> dg_t.
  Parameter dg_ederef: dg_t -> dg_t.
  Parameter dg_eassign_l: dg_t -> dg_t.
  Parameter dg_eassign_r: dg_t -> dg_t.
  Parameter dg_erun: dg_t -> dg_t.
  Parameter dg_elift: dg_t -> dg_t.
  Parameter dg_ebox: dg_t -> dg_t.

  (** Terms Mapping *)
  Parameter cast_econst: dg_t -> nat -> T.expr.
  Parameter cast_evar: dg_t -> T.var -> T.expr.
  Parameter cast_eabs: dg_t -> T.var -> T.expr -> T.expr.
  Parameter cast_efix: dg_t -> T.var -> T.var -> T.expr -> T.expr.
  Parameter cast_eapp: dg_t -> T.expr -> T.expr -> T.expr.
  Parameter cast_eloc: dg_t -> S.location -> T.expr.
  Parameter cast_eref: dg_t -> T.expr -> T.expr.
  Parameter cast_ederef: dg_t -> T.expr -> T.expr.
  Parameter cast_eassign: dg_t -> T.expr -> T.expr -> T.expr.
  Parameter cast_ebox: dg_t -> T.expr -> T.expr.
  Parameter cast_eunbox: dg_t -> T.expr -> T.expr.
  Parameter cast_erun: dg_t -> T.expr -> T.expr.
  Parameter cast_elift: dg_t -> T.expr -> T.expr.

  Parameter ret : dg_t -> T.expr -> T.expr.
  Parameter bind : dg_t -> T.expr -> (T.expr -> T.expr) -> T.expr.

  Parameter ssubst : nat -> StageSet.t -> var -> expr -> expr -> expr.
  Parameter bv : nat -> expr -> VarSet.t.

  (** Var Translation *)
  Parameter cast_var: S.var -> T.var.

  (** Abstract Reduction step *)
  Parameter astep : relation T.state.

End Monad.

