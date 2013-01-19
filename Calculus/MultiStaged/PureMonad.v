Require Import Coq.Relations.Relation_Definitions.
Require Import "Calculus/Sets".
Require Import "Calculus/Definitions".
Require Import "Calculus/Monad".
Require Import "Calculus/MultiStaged/Definitions".
Require Import "Calculus/MultiStaged/Monad".

Module Type PureMonad (R:Replacement) (S:ReplacementCalculus R) 
  (T:StagedCalculus).

  Import T.

  (** Terms Mapping *)
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

End PureMonad.

Module Type PureToMonad (R:Replacement) 
  (S:ReplacementCalculus R) (T:StagedCalculus) 
  (PM:PureMonad R S T) <: Monad R S T.

  Import T.

  (** Data Gathering *)
  Definition dg_t := nat.
  Definition dg_empty := 0.
  Definition dg_id := fun (dg:dg_t) => dg.
  Definition dg_eabs := fun (dg:dg_t) (x:S.var) => dg.
  Definition dg_efix := fun (dg:dg_t) (f:S.var) (x:S.var) => dg.
  Definition dg_eapp_l := dg_id.
  Definition dg_eapp_r:= dg_id.
  Definition dg_eref := dg_id.
  Definition dg_ederef := dg_id.
  Definition dg_eassign_l := dg_id.
  Definition dg_eassign_r := dg_id.
  Definition dg_erun := dg_id.
  Definition dg_elift := dg_id.
  Definition dg_ebox := fun (dg:dg_t) => dg_empty.

  (** Terms Mapping *)
  Definition cast_econst := fun (dg:dg_t) => PM.cast_econst.
  Definition cast_evar := fun (dg:dg_t) => PM.cast_evar.
  Definition cast_eabs := fun (dg:dg_t) => PM.cast_eabs.
  Definition cast_efix := fun (dg:dg_t) => PM.cast_efix.
  Definition cast_eapp := fun (dg:dg_t) => PM.cast_eapp.
  Definition cast_eloc := fun (dg:dg_t) => PM.cast_eloc.
  Definition cast_eref := fun (dg:dg_t) => PM.cast_eref.
  Definition cast_ederef := fun (dg:dg_t) => PM.cast_ederef.
  Definition cast_eassign := fun (dg:dg_t) => PM.cast_eassign.
  Definition cast_ebox := fun (dg:dg_t) => PM.cast_ebox.
  Definition cast_eunbox := fun (dg:dg_t) => PM.cast_eunbox.
  Definition cast_erun := fun (dg:dg_t) => PM.cast_erun.
  Definition cast_elift := fun (dg:dg_t) => PM.cast_elift.

  Definition ret := fun (dg:dg_t) => PM.ret.
  Definition bind := fun (dg:dg_t) => PM.bind.

  Definition ssubst := PM.ssubst.
  Definition bv := PM.bv.

  (** Var Translation *)
  Definition cast_var := PM.cast_var.

  (** Abstract Reduction step *)
  Definition astep := PM.astep.

End PureToMonad.

Module PureToMonadImpl (R:Replacement) 
  (S:ReplacementCalculus R) (T:StagedCalculus) 
  (PM:PureMonad R S T).

  Include PureToMonad R S T PM.

End PureToMonadImpl.

