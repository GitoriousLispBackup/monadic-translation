Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Relations.Relation_Definitions.
Require Import "Misc/Library".
Require Import "Misc/Tactics".
Require Import "Calculus/Sets".
Require Import "Calculus/Definitions".
Require Import "Calculus/MultiStaged/Definitions".
Require Import "Calculus/MultiStaged/DataGathering".
Require Import "Calculus/MultiStaged/Monad".

(**
  There are two kind of variables:
  - Source variables, corresponding to variables
  already existing in expression
  - Hole variables, corresponding to variables
  created to put unbox content outside expression.

  hole_var and source_var enable us to have disjoint sets
 *)
Definition hole_var (x:nat) : nat := (2*x+1)%nat.
Definition source_var (x:nat) : nat := (2*x)%nat.

Module Type Context (R:Replacement) (S:ReplacementCalculus R) 
  (T:StagedCalculus) (DG:DataGathering R S) (M:Monad R S T DG).

  Import T.
  Import M.
  Import DG.

  Definition t : Type := list (expr * S.var).
  Definition t_stack : Type := list t.

  Definition empty : list t := nil.

  Fixpoint fill (dg:dg_t) (c:t) (e:expr) :=
    match c with
    | nil => e
    | (e1, x) :: c => M.bind dg e1 (fun v => 
        M.cast_eapp dg (M.cast_eabs dg (M.cast_var (hole_var x)) 
          (fill dg c e)) v)
    end.

  Fixpoint merge (cs1 cs2:t_stack) :=
    match cs1, cs2 with
    | nil, _ => cs2
    | _, nil => cs1
    | c1::cs1, c2::cs2 => 
       (c1 ++ c2) :: merge cs1 cs2
    end.

  Fixpoint shift (cs:t_stack) : t * t_stack :=
    match cs with
    | nil => (nil, nil)
    | a :: nil => (a, nil)
    | a :: cs => let (c, cs) := shift cs in
       (c, a :: cs)
    end.

  Fixpoint unshift (cs:t_stack) (c:t) : t_stack :=
    match cs with
    | nil => c :: nil
    | a :: cs => a :: (unshift cs c)
    end.

  Fixpoint context_hole_set (c:t) : VarSet.t :=
    match c with
    | nil => VarSet.empty
    | (e1, x) :: c => VarSet.add x (context_hole_set c)
    end.

  Fixpoint stack_hole_set (cs:t_stack) : VarSet.t :=
    match cs with
    | nil => VarSet.empty
    | c :: cs => VarSet.union (context_hole_set c) (stack_hole_set cs)
    end.

  Inductive congr_context (rel:relation expr) : relation t :=
    | CongrCtx_nil: congr_context rel nil nil
    | CongrCtx_cons: forall (k1 k2:t) (e1 e2:expr) (x:S.var),
        congr_context rel k1 k2 -> rel e1 e2 -> 
        congr_context rel ((e1,x)::k1) ((e2,x)::k2).

  Inductive congr_stack (rel:relation expr) : relation t_stack :=
    | CongrStack_empty: congr_stack rel nil nil
    | CongrStack_context: forall (s1 s2:t_stack) (k1 k2:t),
       congr_stack rel s1 s2 -> congr_context rel k1 k2 ->
       congr_stack rel (k1::s1) (k2::s2).

  Fixpoint ssubst_context (n:nat) (ss:StageSet.t) 
    (x:S.var) (c:t) (v:expr) : t :=
    match c with
    | nil => nil
    | (eh,h) :: c => (ssubst n ss (M.cast_var x) eh v, h) ::
        (ssubst_context n (if beq_nat x (hole_var h)
        then (StageSet.add n ss) else ss) x c v)
    end.

  Fixpoint ssubst_stack (n:nat) (ss:StageSet.t) 
    (x:S.var) (cs:t_stack) (v:expr) : t_stack :=
    match cs with
    | nil => nil
    | c :: cs => (ssubst_context n ss x c v) ::
       (ssubst_stack (pred n) (StageSet.remove n ss) x cs v)
    end.

End Context.

Module ContextImpl (R:Replacement) (S:ReplacementCalculus R) 
    (T:StagedCalculus) (DG:DataGathering R S) (M:Monad R S T DG) : 
    Context R S T DG M.
  Include Context R S T DG M.
End ContextImpl.

(* Translation R S T <: StagedTranslation S T. *)
Module Type Translation (R:Replacement) (S:ReplacementCalculus R)
    (T:StagedCalculus) (DG:DataGathering R S) 
    (DGP:DataGatheringPredicates R S DG)
    (DGR:DataGatheringRequirements R S DG DGP) (M:Monad R S T DG). 

  Module Context := ContextImpl R S T DG M.
  Module DGValid := DataGatheringProperties R S DG DGP DGR.
  Import S.CRaw.
  Import DG.

  Fixpoint booker (e:S.expr) (n:nat) : nat :=
    match e with 
    | EConst _ => 0
    | EVar _ => 0
    | EAbs _ e => booker e n
    | EFix _ _ e => booker e n
    | EApp e1 e2 => (booker e1 n + booker e2 n)%nat
    | ELoc _ => 0
    | ERef e => booker e n
    | EDeref e => booker e n
    | EAssign e1 e2 => (booker e1 n + booker e2 n)%nat
    | EBox e => booker e (S n)
    | EUnbox e => match n with
       | 0 => 1
       | S n => booker e n
       end
    | ERun e => booker e n
    | ELift e => booker e n
    end.

  Definition map_iter_booker (e:S.expr) (bs:list nat) (n:nat) :=
    List2.map_iter (fun b n => (b+booker e n)%nat) bs n.

  Fixpoint trans (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t) : T.expr * Context.t_stack :=
    match e with
    | EConst i => (M.ret dg (M.cast_econst dg i), Context.empty)
    | EVar y => (M.ret dg (M.cast_evar dg (M.cast_var (source_var y))), Context.empty)
    | EAbs y e => 
        let (e,cs) := trans e bs (dg_eabs dg y) dgs in
        (M.ret dg (M.cast_eabs dg (M.cast_var (source_var y)) e), cs)
    | EFix f y e => 
        let (e,cs) := trans e bs (dg_efix dg f y) dgs in
        (M.ret dg (M.cast_efix dg
            (M.cast_var (source_var f)) 
            (M.cast_var (source_var y)) e), cs)
    | EApp e1 e2 => 
        let bs2 := map_iter_booker e2 bs 0 in
        let (e1', cs1) := trans e1 bs2 (dg_eapp_l dg) dgs in
        let (e2', cs2) := trans e2 bs (dg_eapp_r dg) dgs in
          (if svalueb 0 e1 then
	   M.bind dg e2' (fun v2 => M.cast_eapp dg 
             (phi e1 bs2 (dg_eapp_l dg) dgs) v2)
	   else M.bind dg e1' (fun v1 => M.bind dg e2'
          (fun v2 => M.cast_eapp dg v1 v2)), 
          Context.merge cs1 cs2)
    | ELoc l => (M.ret dg (M.cast_eloc dg l), Context.empty)
    | ERef e => 
        let (e,cs) := trans e bs (dg_eref dg) dgs in
        (M.bind dg e (fun v => M.cast_eref dg v), cs)
    | EDeref e => 
        let (e,cs) := trans e bs (dg_ederef dg) dgs in
        (M.bind dg e (fun v => M.cast_ederef dg v), cs)
    | EAssign e1 e2 => 
	let bs2 := map_iter_booker e2 bs 0 in
        let (e1', cs1) := trans e1 bs2 (dg_eassign_l dg) dgs in
        let (e2', cs2) := trans e2 bs (dg_eassign_r dg) dgs in
          (if svalueb 0 e1 then
	   M.bind dg e2' (fun v2 => M.cast_eassign dg 
             (phi e1 bs2 (dg_eassign_l dg) dgs) v2)
	   else M.bind dg e1' (fun v1 => M.bind dg e2'
          (fun v2 => M.cast_eassign dg v1 v2)), 
          Context.merge cs1 cs2)
    | EBox e => 
        let (e, cs) := trans e (0 :: bs) (dg_ebox dg) (dg::dgs) in
        match cs with
        | nil => (M.ret dg (M.cast_ebox dg e), Context.empty)
        | c :: cs => (Context.fill dg c (M.ret dg (M.cast_ebox dg e)), cs)
        end
    | EUnbox e =>
        let (b, bs) := List2.hd_cons bs 0 in
        let (dg', dgs') := List2.hd_cons dgs dg_empty in
        let (e', cs) := trans e bs dg' dgs' in
           (M.cast_eunbox dg (M.cast_evar dg 
	   (M.cast_var (hole_var b))), ((e', b) :: nil) :: cs)
    | ERun e =>
        let (e,cs) := trans e bs (dg_erun dg) dgs in
        (M.bind dg e (fun v => M.cast_erun dg v), cs)
    | ELift e =>
        let (e,cs) := trans e bs (dg_elift dg) dgs in
        (M.bind dg e (fun v => M.cast_elift dg v), cs)
    end

  with phi (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t) : T.expr :=
    match e with
    | EConst i => M.cast_econst dg i
    | EVar y => M.cast_evar dg (M.cast_var (source_var y))
    | EAbs y e => 
        let (e, _) := trans e bs (dg_eabs dg y) dgs in
        M.cast_eabs dg (M.cast_var (source_var y)) e
    | EFix f y e => 
        let (e, _) := trans e bs (dg_efix dg f y) dgs in
        M.cast_efix dg
            (M.cast_var (source_var f)) 
            (M.cast_var (source_var y)) e
    | ELoc l => M.cast_eloc dg l
    | EBox e => 
        let (e, _) := trans e (0 :: bs) (dg_ebox dg) (dg::dgs) in
        M.cast_ebox dg e
    | _ => M.cast_econst dg 0
    end.

  Definition trans_expr (e:S.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t) : T.expr :=
    let (e, _) := trans e bs dg dgs in e.

  Fixpoint trans_mem (m:S.Memory.t) (bs:list nat) (dg:dg_t) (dgs:list dg_t) : T.Memory.t :=
    match m with
    | nil => nil
    | e :: m => (phi e bs dg dgs) :: (trans_mem m bs dg dgs)
    end.

  (** ** Administrative Reduction Step *)
  Inductive admin : relation T.expr :=
    | Admin_refl : forall (e:T.expr), admin e e
    | Admin_trans : forall (e1 e2 e3:T.expr), 
        admin e1 e2 -> admin e2 e3 -> admin e1 e3
    | Admin_abs : forall (x:T.var) (e1 e2:T.expr) (dg:dg_t),
        admin e1 e2 -> admin (M.cast_eabs dg x e1) (M.cast_eabs dg x e2)
    | Admin_fix : forall (f x:T.var) (e1 e2:T.expr) (dg:dg_t),
        admin e1 e2 -> admin (M.cast_efix dg f x e1) (M.cast_efix dg f x e2)
    | Admin_app : forall (e1 e2 e3 e4:T.expr) (dg:dg_t),
        admin e1 e3 -> admin e2 e4 -> 
        admin (M.cast_eapp dg e1 e2) (M.cast_eapp dg e3 e4)
    | Admin_ref : forall (e1 e2:T.expr) (dg:dg_t),
        admin e1 e2 -> admin (M.cast_eref dg e1) (M.cast_eref dg e2)
    | Admin_deref : forall (e1 e2:T.expr) (dg:dg_t),
        admin e1 e2 -> admin (M.cast_ederef dg e1) (M.cast_ederef dg e2)
    | Admin_assign : forall (e1 e2 e3 e4:T.expr) (dg:dg_t),
        admin e1 e3 -> admin e2 e4 -> 
        admin (M.cast_eassign dg e1 e2) (M.cast_eassign dg e3 e4)
    | Admin_box : forall (e1 e2:T.expr) (dg:dg_t),
        admin e1 e2 -> admin (M.cast_ebox dg e1) (M.cast_ebox dg e2)
    | Admin_unbox : forall (e1 e2:T.expr) (dg:dg_t),
        admin e1 e2 -> admin (M.cast_eunbox dg e1) (M.cast_eunbox dg e2)
    | Admin_run : forall (e1 e2:T.expr) (dg:dg_t),
        admin e1 e2 -> admin (M.cast_erun dg e1) (M.cast_erun dg e2)
    | Admin_lift : forall (e1 e2:T.expr) (dg:dg_t),
        admin e1 e2 -> admin (M.cast_elift dg e1) (M.cast_elift dg e2)
    | Admin_ret : forall (e1 e2:T.expr) (dg:dg_t),
        admin e1 e2 -> admin (M.ret dg e1) (M.ret dg e2)
    | Admin_bind : forall (e1 e2:T.expr) (f1 f2:T.expr -> T.expr) (dg:dg_t),
        admin e1 e2 -> (forall e3:T.expr, admin (f1 e3) (f2 e3)) ->
        admin (M.bind dg e1 f1) (M.bind dg e2 f2)
   | Admin_unbox_box : forall (e:expr) (*(bs:list nat)*) (dg:dg_t) (dgs:list dg_t),
        svalue 1 e ->
        DGValid.valid_dgs 1 dg (dg_empty :: dgs) ->
        admin (M.cast_eunbox dg (M.cast_ebox dg_empty
          (trans_expr e (0::nil) dg (dg_empty :: dgs)))) 
          (trans_expr e (0::nil) dg (dg_empty :: dgs))
   | Admin_bind_app_phi : forall (v:expr) (e:T.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t), 
       svalue 0 v -> 
       let f := fun v0 => M.bind dg e (fun v1 => M.cast_eapp dg v0 v1) in
       admin (M.bind dg (M.ret (dg_eapp_l dg) (phi v bs (dg_eapp_l dg) dgs)) f) (f (phi v bs (dg_eapp_l dg) dgs))
  | Admin_bind_assign_phi : forall (v:expr) (e:T.expr) (bs:list nat) (dg:dg_t) (dgs:list dg_t), 
       svalue 0 v ->
       let f := fun v0 => M.bind dg e (fun v1 => M.cast_eassign dg v0 v1) in
       admin (M.bind dg (M.ret (dg_eassign_l dg) (phi v bs (dg_eassign_l dg) dgs)) f) (f (phi v bs (dg_eassign_l dg) dgs)).

  Definition admin_context :  relation Context.t := 
    Context.congr_context admin.
  Definition admin_stack : relation Context.t_stack := 
    Context.congr_stack admin.

  (** ** Relative Abstract Reduction Step *)
  Inductive rstep : relation T.state :=
    | Rel_step : forall (s:T.state) (e1 e2:T.expr) (M:T.Memory.t),
        M.astep s (M,e1) -> admin e1 e2 -> rstep s (M,e2).

End Translation.

Module TranslationImpl (R:Replacement) 
   (S:ReplacementCalculus R) (T:StagedCalculus) 
   (DG:DataGathering R S) (DGP:DataGatheringPredicates R S DG)  
   (DGR:DataGatheringRequirements R S DG DGP) 
   (M:Monad R S T DG) <: Translation R S T DG DGP DGR M.
  Include Translation R S T DG DGP DGR M.
End TranslationImpl.
