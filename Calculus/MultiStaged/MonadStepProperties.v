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
Require Import "Calculus/MultiStaged/DataGathering".

(* TODO: Create a UniformMonadProperties type *)
Module Type MonadStepProperties (R:Replacement) 
  (S:ReplacementCalculus R) (T:StagedCalculus)
  (DG:DataGathering R S) (DGP:DataGatheringPredicates R S DG) 
  (DGR:DataGatheringRequirements R S DG DGP) 
  (M:Monad R S T DG).

  Module Translation := TranslationImpl R S T DG DGP DGR M.
  Import Translation.
  Import T.
  Import M.
  Import DG.
  Import DGP.
  Import DGR.

  (** Data Gathering Properties *)

  (**
  The following properties ensure that data gathering
  over values won't have effect on the translation of the value.
  In the case of free variables replacement, we can assume
  that we have Barendregt Property.
  *)

  Parameter dg_svalue_trans :
    forall (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    S.svalue 1 e ->
    dg_comp (dg_ebox dg_empty) dg ->
    trans e bs (dg_ebox dg_empty) dgs  = trans e bs dg dgs.

  (** Substitution Properties *)

  Parameter ssubst_ret :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr) (dg:dg_t),
     ssubst n ss (cast_var x) (ret dg e) v = ret dg (ssubst n ss (cast_var x) e v).

  Parameter ssubst_bind :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e1 v:expr) (f1 f2: expr -> expr) (dg:dg_t),
     (forall v2, ssubst n ss (cast_var x) (f1 v2) v = 
       f2 (ssubst n ss (cast_var x) v2 v)) ->
     ssubst n ss (cast_var x) (bind dg e1 f1) v = 
       bind dg (ssubst n ss (cast_var x) e1 v) f2.

  Parameter ssubst_econst :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (c:nat) (v:expr) (dg:dg_t),
     ssubst n ss (cast_var x) (cast_econst dg c) v = cast_econst dg c.

  Parameter ssubst_evar :
    forall (n:nat) (ss:StageSet.t) (x y:S.var) (v:expr) (dg:dg_t),
     ssubst n ss (cast_var x) (cast_evar dg (cast_var y)) v = 
     if beq_nat x y && S.CRaw.BindingSet.rho n ss 
     then v else (cast_evar dg (cast_var y)).

  Parameter ssubst_eabs :
    forall (n:nat) (ss:StageSet.t) (x y:S.var) (e v:expr) (dg:dg_t),
     ssubst n ss (cast_var x) (cast_eabs dg (cast_var y) e) v = 
     cast_eabs dg (cast_var y) (ssubst n (if S.beq_var x y 
        then (StageSet.add n ss) else ss) (cast_var x) e v).

  Parameter ssubst_efix :
    forall (n:nat) (ss:StageSet.t) (x f y:S.var) (e v:expr) (dg:dg_t),
     ssubst n ss (cast_var x) (cast_efix dg (cast_var f) (cast_var y) e) v = 
     cast_efix dg (cast_var f) (cast_var y) (ssubst n (if orb (S.beq_var x f) (S.beq_var x y) 
        then (StageSet.add n ss) else ss) (cast_var x) e v).

  Parameter ssubst_eapp :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e1 e2 v:expr) (dg:dg_t),
     ssubst n ss (cast_var x) (cast_eapp dg e1 e2) v
       = cast_eapp dg (ssubst n ss (cast_var x) e1 v) 
         (ssubst n ss (cast_var x) e2 v).

  Parameter ssubst_eloc :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (l:nat) (v:expr) (dg:dg_t),
     ssubst n ss (cast_var x) (cast_eloc dg l) v = cast_eloc dg l.

  Parameter ssubst_eref :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr) (dg:dg_t),
     ssubst n ss (cast_var x) (cast_eref dg e) v
       = cast_eref dg (ssubst n ss (cast_var x) e v).

  Parameter ssubst_ederef :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr) (dg:dg_t),
     ssubst n ss (cast_var x) (cast_ederef dg e) v
       = cast_ederef dg (ssubst n ss (cast_var x) e v).

  Parameter ssubst_eassign :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e1 e2 v:expr) (dg:dg_t),
     ssubst n ss (cast_var x) (cast_eassign dg e1 e2) v
       = cast_eassign dg (ssubst n ss (cast_var x) e1 v) 
         (ssubst n ss (cast_var x) e2 v).

  Parameter ssubst_ebox :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr) (dg:dg_t),
     ssubst n ss (cast_var x) (cast_ebox dg e) v
       = cast_ebox dg (ssubst (S n) ss (cast_var x) e v).

  Parameter ssubst_eunbox :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr) (dg:dg_t),
     ssubst n ss (cast_var x) (cast_eunbox dg e) v
       = cast_eunbox dg (ssubst (pred n) (StageSet.remove n ss) (cast_var x) e v).

  Parameter ssubst_erun :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr) (dg:dg_t),
     ssubst n ss (cast_var x) (cast_erun dg e) v
       = cast_erun dg (ssubst n ss (cast_var x) e v).

  Parameter ssubst_elift :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr) (dg:dg_t),
     ssubst n ss (cast_var x) (cast_elift dg e) v
       = cast_elift dg (ssubst n ss (cast_var x) e v).

  (** Abstract Reduction Properties *)

  Parameter astep_bind_app :
    forall (e1 e2 ef:expr) (M1 M2:Memory.t) (dg:dg_t),
    let f := fun v1 => bind dg ef (fun v2 : T.expr => cast_eapp dg v1 v2) in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind dg e1 f) (M2, bind dg e2 f).

  Parameter astep_bind_app_svalue :
    forall (v:S.expr) (e1 e2:expr) (M1 M2:Memory.t) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    S.svalue 0 v ->
    let f := fun v1 => cast_eapp dg (phi v bs (dg_eapp_l dg) dgs) v1 in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind dg e1 f) (M2, bind dg e2 f).

  (* Todo: remove those two clauses *)
  Parameter astep_bind_app_eabs :
    forall (e1 e2 ef:expr) (M1 M2:Memory.t) (x:var) (dg:dg_t),
    let f := fun v => cast_eapp dg (cast_eabs (dg_eapp_l dg) x ef) v in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind dg e1 f) (M2, bind dg e2 f).

  Parameter astep_bind_app_efix :
    forall (e1 e2 ef:expr) (M1 M2:Memory.t) (f x:var) (dg:dg_t),
    let f := fun v => cast_eapp dg (cast_efix (dg_eapp_l dg) f x ef) v in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind dg e1 f) (M2, bind dg e2 f).

  Parameter astep_bind_eref :
    forall (e1 e2:expr) (M1 M2:Memory.t) (dg:dg_t),
    let f := fun v => cast_eref dg v in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind dg e1 f) (M2, bind dg e2 f).

  Parameter astep_bind_ederef :
    forall (e1 e2:expr) (M1 M2:Memory.t) (dg:dg_t),
    let f := fun v => cast_ederef dg v in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind dg e1 f) (M2, bind dg e2 f).

  Parameter astep_bind_assign :
    forall (e1 e2 ef:expr) (M1 M2:Memory.t) (dg:dg_t),
    let f := fun v1 => bind dg ef (fun v2 : T.expr => cast_eassign dg v1 v2) in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind dg e1 f) (M2, bind dg e2 f).

  Parameter astep_bind_assign_svalue :
    forall (v:S.expr) (e1 e2:expr) (M1 M2:Memory.t) (bs:list nat) (dg:dg_t) (dgs:list dg_t),
    S.svalue 0 v ->
    let f := fun v1 => cast_eassign dg (phi v bs (dg_eassign_l dg) dgs) v1 in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind dg e1 f) (M2, bind dg e2 f).

  Parameter astep_bind_erun :
    forall (e1 e2:expr) (M1 M2:Memory.t) (dg:dg_t),
    let f := fun v => cast_erun dg v in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind dg e1 f) (M2, bind dg e2 f).

  Parameter astep_bind_elift :
    forall (e1 e2:expr) (M1 M2:Memory.t) (dg:dg_t),
    let f := fun v => cast_elift dg v in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind dg e1 f) (M2, bind dg e2 f).

  Parameter astep_bind_1 :
    forall (v:S.expr) (e1 e2:expr) (bs:list nat) (M1 M2:Memory.t) 
      (f:expr -> expr) (dg:dg_t) (dgs:list dg_t),
    S.svalue 0 v -> astep (M1, e1) (M2, e2) ->
    admin e2 (ret dg (phi v bs dg dgs)) ->
    astep (M1, (bind dg e1 f)) (M2, (f (phi v bs dg dgs))).

  Parameter astep_bind_2 :
    forall (v:S.expr) (e:expr) (bs:list nat) (M1 M2:Memory.t) 
      (f:expr -> expr) (dg:dg_t) (dgs:list dg_t),
    S.svalue 0 v -> astep (M1, (f (phi v bs dg dgs))) (M2, e) ->
    astep (M1, (bind dg (ret dg (phi v bs dg dgs)) f)) (M2, e).

  (* Weakest version: checked *)
  (* This is used in EBox, n=1 case *)
  Parameter astep_app_abs_hole:
    forall (e1 eh:S.expr) (e:T.expr) (h:S.var) (t:Context.t) (M:S.Memory.t),
    S.svalue 0 eh -> S.depth eh = 0 ->
    S.memory_svalue 0 M -> S.memory_depth M = 0 ->
    (e, ((trans_expr eh (0 :: nil) dg_empty nil, h) :: t) :: nil) =
          trans e1 (0 :: nil) (dg_ebox dg_empty) (dg_empty :: nil) ->
    astep (trans_mem M nil dg_empty nil, cast_eapp dg_empty
      (cast_eabs dg_empty (cast_var (hole_var h))
       (Context.fill dg_empty t (ret dg_empty (cast_ebox dg_empty e))))
       (phi eh nil dg_empty nil))
       (trans_mem M nil dg_empty nil,
       ssubst 0 StageSet.empty (cast_var (hole_var h))
       (Context.fill dg_empty t (ret dg_empty (cast_ebox dg_empty e))) 
       (phi eh nil dg_empty nil)).

  (* Weakest version: checked *)
  (* This is used in EApp(EAbs), n=0 case *)
  Parameter astep_app_abs :
    forall (v:S.expr) (x:S.var) (e:S.expr) (M:S.Memory.t),
    S.memory_svalue 0 M -> S.memory_depth M = 0 -> S.depth e = 0 ->
    S.depth v = 0 -> S.svalue 0 v ->
    astep (trans_mem M nil dg_empty nil, cast_eapp dg_empty
      (cast_eabs dg_empty (cast_var x) (trans_expr e nil dg_empty nil)) (phi v nil dg_empty nil))
      (trans_mem M nil dg_empty nil, 
      ssubst 0 StageSet.empty (cast_var x) (trans_expr e nil dg_empty nil) (phi v nil dg_empty nil)).

  (* Weakest version: checked *)
  (* This is used in EApp(EFix), n=0 case *)
  Parameter astep_app_fix :
    forall (v:S.expr) (f x:S.var) (e:S.expr) (M:S.Memory.t),
    S.memory_svalue 0 M -> S.memory_depth M = 0 -> S.depth e = 0 ->
    S.depth v = 0 -> S.svalue 0 v -> 
    astep (trans_mem M nil dg_empty nil, cast_eapp dg_empty
      (cast_efix dg_empty (cast_var f) (cast_var x) (trans_expr e nil dg_empty nil)) (phi v nil dg_empty nil))
      (trans_mem M nil dg_empty nil, ssubst 0 StageSet.empty (cast_var f)
      (ssubst 0 StageSet.empty (cast_var x) (trans_expr e nil dg_empty nil) (phi v nil dg_empty nil))
      (cast_efix dg_empty (cast_var f) (cast_var x) (trans_expr e nil dg_empty nil))).

  (* Weakest version: checked *)
  (* This is used in EAssign(ELoc), n=0 case *)
  Parameter astep_assign_loc :
    forall (v:S.expr) (l:S.location) (M:S.Memory.t),
    S.memory_svalue 0 M -> S.memory_depth M = 0 -> 
    S.depth v = 0 -> S.svalue 0 v -> l < length M ->
    astep (trans_mem M nil dg_empty nil, 
      cast_eassign dg_empty (cast_eloc dg_empty l) (phi v nil dg_empty nil)) 
      (trans_mem (S.Memory.set l v M) nil dg_empty nil, ret dg_empty (phi v nil dg_empty nil)).

  (* Weakest version: checked *)
  (* This is used in ERef, n=0 case *)
  Parameter astep_eref :
    forall (v:S.expr) (M:S.Memory.t),
    S.memory_svalue 0 M -> S.memory_depth M = 0 -> 
    S.depth v = 0 -> S.svalue 0 v ->
    astep (trans_mem M nil dg_empty nil, cast_eref dg_empty (phi v nil dg_empty nil))
    (Memory.set (Memory.fresh (trans_mem M nil dg_empty nil)) (phi v nil dg_empty nil) 
    (trans_mem M nil dg_empty nil),
      ret dg_empty (cast_eloc dg_empty (Memory.fresh (trans_mem M nil dg_empty nil)))).
    
  (* Weakest version: checked *)
  (* This is used in EDeref, n=0 case *)
  Parameter astep_ederef :
    forall (l:S.location) (M:S.Memory.t),
    S.memory_svalue 0 M -> S.memory_depth M = 0 -> 
    l < length M ->
    astep (trans_mem M nil dg_empty nil, cast_ederef dg_empty (cast_eloc dg_empty l)) 
    (trans_mem M nil dg_empty nil, ret dg_empty (Memory.get l (trans_mem M nil dg_empty nil))).

  (* Weakest version: checked *)
  (* This is used in ERun, n=0 case *)
  Parameter astep_erun :
    forall (M:S.Memory.t) (e:S.expr),
    S.memory_svalue 0 M -> S.memory_depth M = 0 -> 
    S.svalue 1 e ->
    astep (trans_mem M nil dg_empty nil, cast_erun dg_empty (cast_ebox dg_empty
    (trans_expr e nil (dg_ebox dg_empty) (dg_empty::nil)))) 
    (trans_mem M nil dg_empty nil, trans_expr e nil dg_empty nil).

  (* Weakest version: checked *)
  (* This is used in ELift, n=0 case *)
  Parameter astep_elift :
    forall (M:S.Memory.t) (v:S.expr),
    S.memory_svalue 0 M -> S.memory_depth M = 0 -> 
    S.depth v = 0 -> S.svalue 0 v ->
    astep (trans_mem M nil dg_empty nil, cast_elift dg_empty (phi v nil dg_empty nil)) 
    (trans_mem M nil dg_empty nil, ret dg_empty (cast_ebox dg_empty (ret (dg_ebox dg_empty) (phi v nil (dg_ebox dg_empty) (dg_empty::nil))))).

End MonadStepProperties.
