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

(* TODO: Create a UniformMonadProperties type *)
Module Type MonadStepProperties (R:Replacement) 
  (T:StagedCalculus) (M:Monad R T).

  Module Translation := TranslationImpl R T M.
  Import Translation.
  Import T.
  Import M.

  (** Substitution Properties *)

  Parameter ssubst_ret :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (ret e) v = ret (ssubst n ss (cast_var x) e v).

  Parameter ssubst_bind :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e1 v:expr) (f1 f2: expr -> expr),
     (forall v2, ssubst n ss (cast_var x) (f1 v2) v = 
       f2 (ssubst n ss (cast_var x) v2 v)) ->
     ssubst n ss (cast_var x) (bind e1 f1) v = 
       bind (ssubst n ss (cast_var x) e1 v) f2.

  Parameter ssubst_econst :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (c:nat) (v:expr),
     ssubst n ss (cast_var x) (cast_econst c) v = cast_econst c.

  Parameter ssubst_evar :
    forall (n:nat) (ss:StageSet.t) (x y:S.var) (v:expr),
     ssubst n ss (cast_var x) (cast_evar (cast_var y)) v = 
     if beq_nat x y && S.CRaw.BindingSet.rho n ss 
     then v else (cast_evar (cast_var y)).

  Parameter ssubst_eabs :
    forall (n:nat) (ss:StageSet.t) (x y:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_eabs (cast_var y) e) v = 
     cast_eabs (cast_var y) (ssubst n (if S.beq_var x y 
        then (StageSet.add n ss) else ss) (cast_var x) e v).

  Parameter ssubst_efix :
    forall (n:nat) (ss:StageSet.t) (x f y:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_efix (cast_var f) (cast_var y) e) v = 
     cast_efix (cast_var f) (cast_var y) (ssubst n (if orb (S.beq_var x f) (S.beq_var x y) 
        then (StageSet.add n ss) else ss) (cast_var x) e v).

  Parameter ssubst_eapp :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e1 e2 v:expr),
     ssubst n ss (cast_var x) (cast_eapp e1 e2) v
       = cast_eapp (ssubst n ss (cast_var x) e1 v) 
         (ssubst n ss (cast_var x) e2 v).

  Parameter ssubst_eloc :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (l:nat) (v:expr),
     ssubst n ss (cast_var x) (cast_eloc l) v = cast_eloc l.

  Parameter ssubst_eref :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_eref e) v
       = cast_eref (ssubst n ss (cast_var x) e v).

  Parameter ssubst_ederef :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_ederef e) v
       = cast_ederef (ssubst n ss (cast_var x) e v).

  Parameter ssubst_eassign :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e1 e2 v:expr),
     ssubst n ss (cast_var x) (cast_eassign e1 e2) v
       = cast_eassign (ssubst n ss (cast_var x) e1 v) 
         (ssubst n ss (cast_var x) e2 v).

  Parameter ssubst_ebox :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_ebox e) v
       = cast_ebox (ssubst (S n) ss (cast_var x) e v).

  Parameter ssubst_eunbox :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_eunbox e) v
       = cast_eunbox (ssubst (pred n) (StageSet.remove n ss) (cast_var x) e v).

  Parameter ssubst_erun :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_erun e) v
       = cast_erun (ssubst n ss (cast_var x) e v).

  Parameter ssubst_elift :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_elift e) v
       = cast_elift (ssubst n ss (cast_var x) e v).

  (** Abstract Reduction Properties *)

  Parameter astep_bind_app :
    forall (e1 e2 ef:expr) (M1 M2:Memory.t),
    let f := fun v1 => bind ef (fun v2 : T.expr => cast_eapp v1 v2) in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind e1 f) (M2, bind e2 f).

  Parameter astep_bind_app_svalue :
    forall (v:S.expr) (e1 e2:expr) (M1 M2:Memory.t) (bs:list nat),
    S.svalue 0 v ->
    let f := fun v1 => cast_eapp (phi v bs) v1 in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind e1 f) (M2, bind e2 f).

  (* Todo: remove those two clauses *)
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

  Parameter astep_bind_assign_svalue :
    forall (v:S.expr) (e1 e2:expr) (M1 M2:Memory.t) (bs:list nat),
    S.svalue 0 v ->
    let f := fun v1 => cast_eassign (phi v bs) v1 in
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

  (* Weakest version: Checked *)
  Parameter astep_assign_loc :
    forall (v:S.expr) (l:S.location) (bs:list nat) (M:S.Memory.t),
    S.memory_svalue 0 M -> S.memory_depth M = 0 -> 
    S.svalue 0 v -> l < length M ->
    astep (trans_mem M bs, cast_eassign (cast_eloc l) 
    (phi v bs)) (trans_mem (S.Memory.set l v M) bs, ret (phi v bs)).

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

  Parameter astep_elift :
    forall (M:Memory.t) (e:S.expr) (bs:list nat),
    S.svalue 0 e ->
    astep (M, cast_elift (phi e bs)) (M, ret (cast_ebox (ret (phi e bs)))).

End MonadStepProperties.
