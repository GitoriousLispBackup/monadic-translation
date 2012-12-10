Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.MinMax.
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

Module Context (R:Replacement) (T:StagedCalculus) (M:Monad R T).

  Import T.
  Import M.

  Definition t : Type := list (expr * M.S.var).
  Definition t_stack : Type := list t.

  Definition empty : list t := nil.

  Fixpoint fill (c:t) (e:expr) :=
    match c with
    | nil => e
    | (e1, x) :: c => M.bind e1 (fun v => 
        M.cast_eapp (M.cast_eabs (M.cast_var (hole_var x)) (fill c e)) v)
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
    | CongrCtx_cons: forall (k1 k2:t) (e1 e2:expr) (x:M.S.var),
        congr_context rel k1 k2 -> rel e1 e2 -> 
        congr_context rel ((e1,x)::k1) ((e2,x)::k2).

  Inductive congr_stack (rel:relation expr) : relation t_stack :=
    | CongrStack_empty: congr_stack rel nil nil
    | CongrStack_context: forall (s1 s2:t_stack) (k1 k2:t),
       congr_stack rel s1 s2 -> congr_context rel k1 k2 ->
       congr_stack rel (k1::s1) (k2::s2).

  Fixpoint ssubst_context (n:nat) (ss:StageSet.t) 
    (x:M.S.var) (c:t) (v:expr) : t :=
    match c with
    | nil => nil
    | (eh,h) :: c => (ssubst n ss (M.cast_var x) eh v, h) ::
        (ssubst_context n (if beq_nat x (hole_var h)
        then (StageSet.add n ss) else ss) x c v)
    end.

  Fixpoint ssubst_stack (n:nat) (ss:StageSet.t) 
    (x:M.S.var) (cs:t_stack) (v:expr) : t_stack :=
    match cs with
    | nil => nil
    | c :: cs => (ssubst_context n ss x c v) ::
       (ssubst_stack (pred n) (StageSet.remove n ss) x cs v)
    end.

End Context.

(* Translation R T <: StagedTranslation (Calculus R) T. *)
Module Translation (R:Replacement) 
    (T:StagedCalculus) (M:Monad R T). 

  Module S := M.S.
  Module Context := Context R T M.
  Import S.CRaw.

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

  Fixpoint trans (e:S.expr) (bs:list nat) : T.expr * Context.t_stack :=
    match e with
    | EConst i => (M.ret (M.cast_econst i), Context.empty)
    | EVar y => (M.ret (M.cast_evar (M.cast_var (source_var y))), Context.empty)
    | EAbs y e => 
        let (e,cs) := trans e bs in
        (M.ret (M.cast_eabs (M.cast_var (source_var y)) e), cs)
    | EFix f y e => 
        let (e,cs) := trans e bs in
        (M.ret (M.cast_efix 
            (M.cast_var (source_var f)) 
            (M.cast_var (source_var y)) e), cs)
    | EApp e1 e2 => 
        let bs2 := map_iter_booker e2 bs 0 in
        let (e1, cs1) := trans e1 bs2 in
        let (e2, cs2) := trans e2 bs in
          (M.bind e1 (fun v1 => M.bind e2
          (fun v2 => M.cast_eapp v1 v2)), 
          Context.merge cs1 cs2)
    | ELoc l => (M.ret (M.cast_eloc l), Context.empty)
    | ERef e => 
        let (e,cs) := trans e bs in
        (M.bind e (fun v => M.cast_eref v), cs)
    | EDeref e => 
        let (e,cs) := trans e bs in
        (M.bind e (fun v => M.cast_ederef v), cs)
    | EAssign e1 e2 => 
	let bs2 := map_iter_booker e2 bs 0 in
        let (e1, cs1) := trans e1 bs2 in
        let (e2, cs2) := trans e2 bs in
          (M.bind e1 (fun v1 => M.bind e2
          (fun v2 => M.cast_eassign v1 v2)), 
          Context.merge cs1 cs2)
    | EBox e => 
        let (e, cs) := trans e (0 :: bs) in
        match cs with
        | nil => (M.ret (M.cast_ebox e), Context.empty)
        | c :: cs => (Context.fill c (M.ret (M.cast_ebox e)), cs)
        end
    | EUnbox e =>
        let (b, bs) := List2.hd_cons bs 0 in
        let (e', cs) := trans e bs in
           (M.cast_eunbox (M.cast_evar 
	   (M.cast_var (hole_var b))), ((e', b) :: nil) :: cs)
    | ERun e =>
        let (e,cs) := trans e bs in
        (M.bind e (fun v => M.cast_erun v), cs)
    | ELift e =>
        let (e,cs) := trans e bs in
        (M.bind e (fun v => M.cast_elift v), cs)
    end.

  Definition trans_expr (e:S.expr) (bs:list nat) : T.expr :=
    let (e, _) := trans e bs in e.

  Definition phi (e:S.expr) (bs:list nat) : T.expr :=
    match e with
    | EConst i => M.cast_econst i
    | EVar y => M.cast_evar (M.cast_var (source_var y))
    | EAbs y e => 
        let (e, _) := trans e bs in
        M.cast_eabs (M.cast_var (source_var y)) e
    | EFix f y e => 
        let (e, _) := trans e bs in
        M.cast_efix 
            (M.cast_var (source_var f)) 
            (M.cast_var (source_var y)) e
    | ELoc l => M.cast_eloc l
    | EBox e => 
        let (e, _) := trans e (0 :: bs) in
        M.cast_ebox e
    | _ => M.cast_econst 0
    end.

  Fixpoint trans_mem (m:S.Memory.t) (bs:list nat) : T.Memory.t :=
    match m with
    | nil => nil
    | e :: m => phi e bs :: (trans_mem m bs)
    end.

  (** ** Administrative Reduction Step *)
  Inductive admin : relation T.expr :=
    | Admin_refl : forall (e:T.expr), admin e e
    | Admin_trans : forall (e1 e2 e3:T.expr) (acc:nat -> nat), 
        admin e1 e2 -> admin e2 e3 -> admin e1 e3
    | Admin_abs : forall (x:T.var) (e1 e2:T.expr),
        admin e1 e2 -> admin (M.cast_eabs x e1) (M.cast_eabs x e2)
    | Admin_fix : forall (f x:T.var) (e1 e2:T.expr),
        admin e1 e2 -> admin (M.cast_efix f x e1) (M.cast_efix f x e2)
    | Admin_app : forall (e1 e2 e3 e4:T.expr),
        admin e1 e3 -> admin e2 e4 -> 
        admin (M.cast_eapp e1 e2) (M.cast_eapp e3 e4)
    | Admin_ref : forall (e1 e2:T.expr),
        admin e1 e2 -> admin (M.cast_eref e1) (M.cast_eref e2)
    | Admin_deref : forall (e1 e2:T.expr),
        admin e1 e2 -> admin (M.cast_ederef e1) (M.cast_ederef e2)
    | Admin_assign : forall (e1 e2 e3 e4:T.expr),
        admin e1 e3 -> admin e2 e4 -> 
        admin (M.cast_eassign e1 e2) (M.cast_eassign e3 e4)
    | Admin_box : forall (e1 e2:T.expr),
        admin e1 e2 -> admin (M.cast_ebox e1) (M.cast_ebox e2)
    | Admin_unbox : forall (e1 e2:T.expr),
        admin e1 e2 -> admin (M.cast_eunbox e1) (M.cast_eunbox e2)
    | Admin_run : forall (e1 e2:T.expr),
        admin e1 e2 -> admin (M.cast_erun e1) (M.cast_erun e2)
    | Admin_lift : forall (e1 e2:T.expr),
        admin e1 e2 -> admin (M.cast_elift e1) (M.cast_elift e2)
    | Admin_ret : forall (e1 e2:T.expr),
        admin e1 e2 -> admin (M.ret e1) (M.ret e2)
    | Admin_bind : forall (e1 e2:T.expr) (f1 f2:T.expr -> T.expr),
        admin e1 e2 -> (forall e3:T.expr, admin (f1 e3) (f2 e3)) ->
        admin (M.bind e1 f1) (M.bind e2 f2)
    | Admin_reduc : forall (e:expr) (bs:list nat), svalue 1 e ->
        admin (M.cast_eunbox (M.cast_ebox (trans_expr e bs))) 
          (trans_expr e bs).

  Definition admin_context :  relation Context.t := 
    Context.congr_context admin.
  Definition admin_stack : relation Context.t_stack := 
    Context.congr_stack admin.

  (** ** Relative Abstract Reduction Step *)
  Inductive rstep : relation T.state :=
    | Rel_step : forall (s:T.state) (e1 e2:T.expr) (M:T.Memory.t),
        M.astep s (M,e1) -> admin e1 e2 -> rstep s (M,e2).

End Translation.

Module Type MonadProperties (R:Replacement) 
  (T:StagedCalculus) (M:Monad R T).

  Module Translation := Translation R T M.
  Import Translation.
  Import T.
  Import M.

  (** Substitution Properties *)

  Parameter ssubst_ret :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (ret e) v = ret (ssubst n ss (cast_var x) e v).

  Parameter ssubst_bind :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e1 v:expr) (f1 f2: expr -> expr),
     ((fun v2 => ssubst n ss (cast_var x) (f1 v2) v) = 
       fun v2 => f2 (ssubst n ss (cast_var x) v2 v)) ->
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

  Parameter astep_bind_erun :
    forall (e1 e2:expr) (M1 M2:Memory.t),
    let f := fun v => cast_erun v in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind e1 f) (M2, bind e2 f).

  Parameter astep_bind_2 :
    forall (v:S.expr) (e:expr) (bs:list nat) (M1 M2:Memory.t) (f:expr -> expr),
    S.svalue 0 v -> astep (M1, (f (phi v bs))) (M2, e) ->
    astep (M1, (bind (ret (phi v bs)) f)) (M2, e).

  Parameter astep_app_abs :
    forall (v:S.expr) (x:S.var) (e:expr) (bs:list nat) (M:Memory.t),
    S.svalue 0 v -> astep (M, cast_eapp
      (cast_eabs (cast_var x) e) (phi v bs))
      (M, ssubst 0 StageSet.empty (cast_var x) e (phi v bs)).

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

End MonadProperties.

Module ContextStaticProperties (R:Replacement)
  (T:StagedCalculus) (M:Monad R T) (MP:MonadProperties R T M).

  Module Context := MP.Translation.Context.
  Import M.
  Import Context.

  Lemma merge_length:
    forall (cs1 cs2:t_stack),
    length (merge cs1 cs2) = max (length cs1) (length cs2).
  Proof.
    induction cs1 ; simpl ; intros.
    reflexivity.
    destruct cs2 ; simpl.
    reflexivity.
    rewrite IHcs1.
    reflexivity.
  Qed.

  Lemma congr_context_app:
    forall (rel:relation T.expr) (c1 c2 c3 c4:t),
    congr_context rel c1 c3 ->
    congr_context rel c2 c4 ->
    congr_context rel (c1++c2) (c3++c4).
  Proof.
    induction c1 ; simpl ; intros.
    inversion H ; subst.
    simpl ; assumption.
    inversion H ; subst.
    constructor.
    apply IHc1 ; assumption.
    assumption.
  Qed.

  Lemma congr_stack_app:
    forall (rel:relation T.expr) (cs1 cs2 cs3 cs4:t_stack),
    congr_stack rel cs1 cs3 ->
    congr_stack rel cs2 cs4 ->
    congr_stack rel (cs1++cs2) (cs3++cs4).
  Proof.
    induction cs1 ; simpl ; intros.
    inversion H ; subst.
    simpl ; assumption.
    inversion H ; subst.
    constructor.
    apply IHcs1 ; assumption.
    assumption.
  Qed.

  Lemma congr_stack_merge:
    forall (rel:relation T.expr) (cs1 cs2 cs3 cs4:t_stack),
    congr_stack rel cs1 cs3 ->
    congr_stack rel cs2 cs4 ->
    congr_stack rel (Context.merge cs1 cs2) (Context.merge cs3 cs4).
  Proof.
    induction cs1 ; simpl ; intros.
    inversion H ; subst.
    simpl ; assumption.
    inversion H ; subst.

    destruct cs2 ;
    inversion H0 ; subst.
    assumption.
    constructor.
    apply IHcs1 ; assumption.
    apply congr_context_app ; assumption.
  Qed.

  Lemma shift_spec:
    forall (cs:t_stack),
    length cs > 0 ->
    let (c, cs') := Context.shift cs in
    cs = cs'++ (c::nil).
  Proof.
    induction cs ; intros ; simpl in *|-*.
    exfalso ; omega.
    destruct cs.
    simpl in *|-* ; reflexivity.
    destruct (shift (t0 :: cs)).
    simpl.
    rewrite IHcs ; simpl ; auto.
    omega.
  Qed.

  Lemma shift_spec_2:
    forall (cs:t_stack),
    let (c, _) := Context.shift cs in
    c = nth (pred (length cs)) cs nil.
  Proof.
    induction cs ; intros ; simpl in *|-*.
    reflexivity.
    destruct (shift cs).
    rewrite IHcs.
    destruct cs ; reflexivity.
  Qed.

  Lemma context_hole_set_app:
    forall (c1 c2:t),
    Context.context_hole_set (c1 ++ c2) =
    VarSet.union (Context.context_hole_set c1)
    (Context.context_hole_set c2).
  Proof.
    induction c1 ; simpl ; intros.
    rewrite VarSetProperties.empty_union_1.
    reflexivity.
    destruct a ; simpl in *|-*.
    rewrite IHc1.
    symmetry ; apply VarSetProperties.union_add.
  Qed.

  Lemma merge_nth:
    forall (cs1 cs2:t_stack) (n:nat),
    nth n (merge cs1 cs2) nil = (nth n cs1 nil ++ nth n cs2 nil).
  Proof.
    induction cs1 ; simpl ; intros.
    destruct n ; reflexivity.
    destruct cs2.
    destruct n ; rewrite app_nil_r ; reflexivity.
    simpl.
    destruct n.
    reflexivity.
    rewrite IHcs1.
    reflexivity.
  Qed.

End ContextStaticProperties.

Module TranslationStaticProperties (R:Replacement) 
    (T:StagedCalculus) (M:Monad R T) (MP:MonadProperties R T M).

  Module Translation := MP.Translation.
  Module CalculusProperties := CalculusProperties R M.S.
  Module ContextStaticProperties := ContextStaticProperties R T M MP.
  Import Translation.
  Import M.S.
  Import M.

  Lemma depth_length:
    forall (e:expr) (bs:list nat),
    let (_, cs) := trans e bs in
    depth e = length cs.
  Proof.
    induction e ; simpl ; intros ;
    try(auto ; fail) ;
    try(specialize (IHe bs) ; destruct (trans e bs) ; auto ; fail) ;

    (* EApp, EAssign *)
    try(
    specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ;
    destruct (trans e1) ; 
    destruct (trans e2) ;
    simpl ; rewrite ContextStaticProperties.merge_length ; auto ; fail).
    
    destruct (depth e).
    specialize (IHe (0::bs)).
    destruct (trans e).
    destruct t ; simpl in *|-*.
    reflexivity.
    inversion IHe.

    specialize (IHe (0::bs)).
    destruct (trans e).
    destruct t ; simpl in *|-*.
    inversion IHe.
    inversion IHe.
    reflexivity.

    destruct (List2.hd_cons bs 0).
    specialize (IHe l).
    destruct (trans e).
    simpl.
    auto.
  Qed.

  Lemma length_svalue:
    forall (e:expr) (bs:list nat) (n:nat),
    let (_, cs) := trans e bs in
    length cs < (S n) <-> svalue (S n) e.
  Proof.
    intros.
    specialize (depth_length e) ; intros.
    specialize (H bs).
    destruct (trans e).
    rewrite <- H.
    apply CalculusProperties.depth_svalue.
  Qed.

  Lemma length_sstep:
    forall (e1 e2:expr) (M1 M2:Memory.t) (bs:list nat),
    sstep (depth e1) (M1,e1) (M2,e2) ->
    memory_depth M1 = 0 ->
    let (_, cs2) := trans e2 bs in
    length cs2 <= depth e1.
  Proof.
    intros.
    specialize (CalculusProperties.depth_sstep_2 M1 e1 M2 e2 H0 H) ; intros.
    destruct H1.
    specialize (depth_length e2 bs) ; intros.
    destruct (trans e2).
    rewrite H3 in *|-*.
    assumption.
  Qed.

  Lemma svalue_phi:
    forall (e:expr) (bs:list nat),
    svalue 0 e -> trans_expr e bs = M.ret (phi e bs).
  Proof.
    intros ; inversion H ; subst ; simpl ;
    try(reflexivity) ;
    try(unfold trans_expr ; simpl ; 
    destruct (trans e0) ; reflexivity).

    unfold trans_expr.
    simpl.
    inversion H ; subst.
    specialize (length_svalue e0 (0::bs) 0) ; intros.
    destruct (trans e0).
    apply H1 in H3.
    destruct t ; simpl in *|-*.
    reflexivity.
    exfalso ; clear H1 H ; omega.
  Qed.

  Lemma context_merge_not_nil:
    forall (t1 t2:Context.t_stack),
    In nil (Context.merge t1 t2) -> In nil t1 \/ In nil t2.
  Proof.
    induction t1 ; intros.
    tauto.
    destruct t2 ; simpl in *|-*.
    tauto.
    destruct H.
    apply app_eq_nil in H.
    tauto.
    apply IHt1 in H.
    tauto.
  Qed.

  Lemma context_stack_not_nil:
    forall (e:expr) (bs:list nat),
    let (_, cs) := trans e bs in
    ~ In nil cs.
  Proof.
    induction e ; intros ; simpl ; auto ;

    try(specialize (IHe bs) ; destruct (trans e) ; auto ; fail) ;

    (* EApp, EAssign *)
    try(
    specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ;
    destruct (trans e1) ; destruct (trans e2) ;
    unfold not ; intros ;
    apply context_merge_not_nil in H ;
    tauto ; fail).


    specialize (IHe (0::bs)).
    destruct (trans e).
    destruct t ; simpl.
    tauto.
    unfold not ; intros ; apply IHe.
    simpl ; auto.
    
    destruct (List2.hd_cons bs 0).
    specialize (IHe l).
    destruct (trans e).
    unfold not ; intros ; apply IHe.
    simpl in *|-*.
    destruct H.
    inversion H.
    assumption.
  Qed.

  Lemma context_shift_not_nil:
    forall (cs:Context.t_stack),
    length cs > 0 ->
    ~ In nil cs ->
    let (c, cs) := Context.shift cs in
    c <> nil /\ ~ In nil cs.
  Proof.
    induction cs ; intros ; simpl in *|-*.
    exfalso ; omega.

    destruct cs ;
    apply not_or_and in H0 ; destruct H0 ; auto.
    destruct (Context.shift (t :: cs)).
    assert(length (t :: cs) > 0).
    simpl ; omega.
    specialize (IHcs H2 H1).
    destruct IHcs.
    clear H ; split.
    assumption.
    simpl ; apply and_not_or ; auto.
  Qed.

  Lemma admin_context_expr:
    forall (k1 k2:Context.t) (e1 e2:T.expr),
    admin_context k1 k2 -> admin e1 e2 ->
    admin (Context.fill k1 e1) (Context.fill k2 e2).
  Proof.
    unfold admin_context ;
    induction k1 ; intros.
    inversion H ; subst.
    simpl in *|-* ; assumption.
    destruct a ; inversion H ; subst.
    simpl ; apply Admin_bind.
    inversion H ; subst.
    assumption.
    
    intros.
    apply Admin_app.
    apply Admin_abs.

    apply IHk1 ; assumption.
    apply Admin_refl.
  Qed.

  Lemma admin_context_app:
    forall (k1 k2 k3 k4:Context.t),
    admin_context k1 k2 -> admin_context k3 k4 ->
    admin_context (k1 ++ k3) (k2 ++ k4).
  Proof.
    intros.
    apply ContextStaticProperties.congr_context_app ; assumption.
  Qed.

  Lemma admin_context_merge:
    forall (cs1 cs2 cs3 cs4:Context.t_stack),
    admin_stack cs1 cs2 ->
    admin_stack cs3 cs4 ->
    admin_stack (Context.merge cs1 cs3) (Context.merge cs2 cs4).
  Proof.
    intros.
    apply ContextStaticProperties.congr_stack_merge ; assumption.
  Qed.
  
  Lemma trans_depth:
    forall (e:expr) (bs bs1 bs2:list nat),
    depth e <= length bs -> trans e (bs++bs1) = trans e (bs++bs2).
  Proof.
    assert(0 <= 0) as Ole.
    auto.
    induction e ; intros ; simpl in *|-* ;

    try(reflexivity) ;
    try(specialize (IHe bs bs1 bs2 H) ; rewrite IHe ; reflexivity) ;

    (* EApp, EAssign *)
    try(destruct bs ; simpl in *|-* ; [
    apply le_n_0_eq in H ; symmetry in H ; apply max_0 in H ;
    destruct H ; rewrite H, H0 in *|-* ;
    specialize (IHe1 nil (map_iter_booker e2 bs1 0) 
      (map_iter_booker e2 bs2 0) Ole) ;
    specialize (IHe2 nil bs1 bs2 Ole) |
    apply max_lub_iff in H ; destruct H ;
    specialize (IHe1 (map_iter_booker e2 (n::bs) 0) 
    (map_iter_booker e2 bs1 (0+(length (n::bs))))
    (map_iter_booker e2 bs2 (0+(length (n::bs))))) ;
    specialize (IHe2 (n::bs) bs1 bs2 H0) ;
    unfold map_iter_booker in *|-* ;
    rewrite List2Properties.length_map_iter in IHe1 ;
    rewrite <- List2Properties.map_iter_app in IHe1 ;
    rewrite <- List2Properties.map_iter_app in IHe1 ] ;
    simpl in *|-* ; rewrite IHe1, IHe2 ; auto ; fail).

    (* EBox *)
    assert(depth e <= S (length bs)).
    omega.
    specialize (IHe (0::bs) bs1 bs2 H0).
    repeat(rewrite app_comm_cons).
    rewrite IHe ; reflexivity.
    
    (* EUnbox *)
    destruct bs ; simpl in *|-*.
    exfalso ; omega.
    apply le_S_n in H.
    specialize (IHe bs bs1 bs2 H).
    rewrite IHe ; reflexivity.
  Qed.

  Lemma trans_depth_0:
    forall (e:expr) (bs1 bs2:list nat),
    depth e = 0 -> trans e bs1 = trans e bs2.
  Proof.
    intros.
    rewrite <- app_nil_l with (l:=bs1).
    rewrite <- app_nil_l with (l:=bs2).
    apply trans_depth.
    simpl ; omega.
  Qed.

  Lemma phi_depth_0:
    forall (v:expr) (bs1 bs2:list nat),
    depth v = 0 -> phi v bs1 = phi v bs2.
  Proof.
    destruct v ; simpl ; intros ; auto.
    rewrite trans_depth_0 with (bs2:=bs2) ; auto.
    rewrite trans_depth_0 with (bs2:=bs2) ; auto.
    specialize (trans_depth v (0::nil) bs1 bs2) ; intros.
    simpl in *|-*.
    rewrite H0 ; auto.
    destruct (depth v) ; simpl in *|-* ; omega.
  Qed.

  Lemma trans_memory_depth_0:
    forall (M:Memory.t) (bs1 bs2:list nat),
    memory_depth M = 0 -> trans_mem M bs1 = trans_mem M bs2.
  Proof.
    induction M ; intros.
    reflexivity.
    simpl in *|-*.
    apply max_0 in H ; destruct H.
    rewrite IHM with (bs2:=bs2) ; auto.
    rewrite phi_depth_0 with (bs2:=bs2) ; auto.
  Qed.

  Lemma booker_depth:
    forall (e:expr) (n:nat),
    depth e <= n -> booker e n = 0.
  Proof.
    induction e ; simpl ; intros ; auto.
    apply max_lub_iff in H.
    destruct H ; rewrite IHe1, IHe2 ; auto.
    apply max_lub_iff in H.
    destruct H ; rewrite IHe1, IHe2 ; auto.
    apply IHe ; omega.
    destruct n ; [exfalso ; omega|auto].
    apply IHe ; omega.
  Qed.

  Lemma booker_ssubst:
    forall (e v:expr) (m n:nat) (x:var) (ss:StageSet.t),
    depth v = 0 ->
    booker (S.ssubst m ss x e v) n = booker e n.
  Proof.
    induction e ; simpl ; intros ; auto.
    destruct (beq_nat x v && CRaw.BindingSet.rho m ss) ; auto.
    apply booker_depth ; omega.
    destruct n ; auto.
  Qed.

  Lemma map_iter_ssubst:
    forall (bs:list nat) (e v:expr) (m n o:nat) (x:var) (ss:StageSet.t),
    depth v = 0 ->
    List2.map_iter (fun b n => (b + booker (S.ssubst m ss x e v) n)%nat) bs o =
    List2.map_iter (fun b n => (b + booker e n)%nat) bs o.
  Proof.
    induction bs ; simpl ; intros ; auto.
    rewrite booker_ssubst ; auto.
    rewrite IHbs ; auto.
  Qed.

    Lemma booker_le:
    forall (e:S.expr) (m n:nat),
    m <= n -> booker e m = 0 -> booker e n = 0.
  Proof.
    induction e ; simpl ; intros ; auto ;
    try(apply IHe with (m:=m) ; auto ; fail) ;
    try(apply plus_is_O in H0 ; destruct H0 ;
    rewrite IHe1 with (m:=m) ; simpl ; auto ; 
    rewrite IHe2 with (m:=m) ; auto ; fail).
    rewrite IHe with (m:=S m) ; omega.
    destruct n.
    apply le_n_0_eq in H ; subst ; auto.
    destruct m ; [inversion H0 |].
    rewrite IHe with (m:=m) ; auto.
    omega.
  Qed.

  Lemma booker_length:
    forall (e:S.expr) (bs:list nat),
    let (_, cs) := trans e bs in
    forall (n:nat),
    booker e n = length (nth n cs nil).
  Proof.
    induction e ; simpl ; intros ; 
    try(destruct n ; auto ; fail) ;
    try(specialize (IHe bs) ;
    destruct (trans e) ; intros ; auto ; fail) ;
    
    try(specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ;
    destruct (trans e1) ; destruct (trans e2) ; intros ;
    rewrite ContextStaticProperties.merge_nth ;
    rewrite app_length ;
    rewrite IHe1, IHe2 ; auto ; fail).

    specialize (IHe (0::bs)).
    destruct (trans e) ; intros.
    destruct t ; intros.
    rewrite booker_le with (m:=n) ; auto.
    destruct n ; auto.
    rewrite IHe ; auto.
    destruct n ; auto.
    specialize (IHe (S n)).
    simpl in IHe ; assumption.

    destruct (List2.hd_cons bs 0).
    specialize (IHe l) ; destruct (trans e) ; intros.
    destruct n0.
    reflexivity.
    simpl.
    apply IHe.
  Qed.

  Lemma length_h:
    forall (e:S.expr) (bs:list nat),
    let (_, cs) := trans e bs in
    length cs <= length bs ->
    forall (n m:nat),
    let c := nth n cs nil in
    let l := length c in
    let (_, h) := nth m c (M.cast_econst 0, (nth n bs 0) + l-m-1) in
    h = (nth n bs 0) + l-m-1.
  Proof.
    assert(forall (m n o p:nat),
      p <= o -> m + n - (o - p) - 1 = m + (p + n) - o - 1) as P1.
    clear ; intros ; omega.

    induction e ; simpl ; intros ;

    try(destruct n ; destruct m ; simpl ; auto ; fail) ;

    try(specialize (IHe bs) ; destruct (trans e) ; intros ;
    specialize (IHe H n m) ; assumption ; fail) ;
    
    try(specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ;
    specialize (booker_length e2 bs) ; intros BookerL ;
    destruct (trans e1) ; destruct (trans e2) ; intros ;
    rewrite ContextStaticProperties.merge_length in H ;
    apply max_lub_iff in H ; destruct H ;
    specialize (IHe2 H0) ;
    unfold map_iter_booker in IHe1 ;
    rewrite List2Properties.length_map_iter in IHe1 ;
    specialize (IHe1 H) ;
    rewrite ContextStaticProperties.merge_nth ;
    rewrite app_length ;
    specialize (le_lt_dec (length (nth n t nil)) m) ; intros ;
    destruct H1 ; [
    rewrite app_nth2 ; auto ;
    specialize (IHe2 n (m - length (nth n t nil))) ;
    simpl in IHe2 ;
    rewrite P1 in IHe2 ; auto |] ;
    rewrite app_nth1 ; auto ;
    specialize (IHe1 n m) ;
    unfold map_iter_booker in *|-* ;
    clear IHe2 ;
    specialize (le_lt_dec (length bs) n) ; intros ;
    destruct H1 ; [
    rewrite nth_overflow with (l:=
    (List2.map_iter (fun b n : nat => (b + booker e2 n)%nat) bs 0)) in IHe1 ;
    [rewrite nth_overflow with (l:=bs) ; auto ;
    rewrite nth_indep with (d':=(cast_econst 0, 0)) in IHe1 ; auto ;
    rewrite nth_indep with (d':=(cast_econst 0, 0)) ; auto ;
    rewrite nth_overflow with (l:=t0) ; auto ; [
    rewrite plus_assoc ; simpl ; rewrite plus_0_r ;
    assumption |
    apply le_trans with (m:=length bs) ; auto ] |] ;
    rewrite List2Properties.length_map_iter ;
    assumption |
    rewrite nth_indep with (d':=(cast_econst 0, 0)) in IHe1 ; auto ;
    rewrite nth_indep with (d':=(cast_econst 0, 0)) ; auto ;
    specialize(List2Properties.map_iter_nth 
    (fun b n => (b + booker e2 n)%nat) bs n 0 0) ; intros ;
    rewrite nth_indep with (d':=0) in H1 ; auto ; [
    rewrite H1 in IHe1 ; clear H1 ;
    rewrite plus_0_r in IHe1 ;
    rewrite <- plus_comm with (m:=length (nth n t nil)) ;
    rewrite plus_assoc ;
    rewrite BookerL in IHe1 ; auto
    | rewrite List2Properties.length_map_iter ; assumption]] ; fail).

    (* Case EBox *)
    specialize (IHe (0::bs)) ;
    destruct (trans e).
    destruct t ; intros.
    destruct m ; destruct n ; simpl ; auto.
    specialize (le_n_S (length t0) (length bs) H) ; intros.
    specialize (IHe H0 (S n) m).
    simpl in IHe.
    assumption.
    
    (* Case EUnbox *)
    destruct bs ; simpl.
    specialize (IHe nil) ;
    destruct (trans e) ; intros.
    simpl in H.
    exfalso ; omega.
    
    specialize (IHe bs) ;
    destruct (trans e) ; intros.
    simpl in H.
    apply le_S_n in H.
    specialize (IHe H (pred n0) m).
    destruct n0.
    simpl.
    destruct m ; auto.
    rewrite <- minus_n_O.
    rewrite plus_minus_n ; auto.
    destruct m ; auto.
    simpl in *|-*.
    destruct n ; assumption.
  Qed.

  Lemma length_h_match:
    forall (e:S.expr) (bs:list nat),
    let (_, cs) := trans e bs in
    length cs <= length bs ->
    match cs with
    | nil => True
    | cs  => let (c, cs') := Context.shift cs in
      match c with
      | nil => True
      | cons (_, h) c' => h = ((nth (pred (length cs)) bs 0) + length c')%nat
      end
    end.
  Proof.
    intros.
    specialize (length_h e bs) ; intros.
    destruct (trans e).
    destruct t ; auto.
    specialize (ContextStaticProperties.shift_spec_2 (t::t0)) ; intros.
    simpl length in *|-*.
    simpl pred in *|-*.
    specialize (H H1 (length t0) 0).
    destruct (Context.shift (t::t0)).
    subst.
    destruct (nth (length t0) (t :: t0) nil) ; auto.
    simpl in *|-*.
    rewrite <- minus_n_O in H.
    simpl in *|-*.
    rewrite plus_minus in H.
    simpl in *|-*.
    rewrite <- minus_n_O in H.
    assumption.
    omega.
  Qed.


End TranslationStaticProperties.

Module ContextProperties (R:Replacement) (T:StagedCalculus) 
    (M:Monad R T) (MP:MonadProperties R T M).

  Module TranslationStaticProperties := TranslationStaticProperties R T M MP.
  Module StaticProperties := TranslationStaticProperties.ContextStaticProperties.
  Module Context := StaticProperties.Context.
  Import StaticProperties.
  Import MP.Translation.
  Import M.
  Import Context.

  Lemma fill_ssubst:
    forall (bs:list nat) (c:t) (n:nat) (ss:StageSet.t) (x:S.var) (v:S.expr) (e:T.expr),
    S.svalue 0 v -> VarSet.mem x (context_hole_set c) = false ->
      fill (ssubst_context n ss (hole_var x) c (phi v bs)) 
      (ssubst n ss (M.cast_var (hole_var x)) e (phi v bs)) = 
      ssubst n ss (cast_var (hole_var x)) (fill c e) (phi v bs).
    intros.
    induction c ; simpl.
    reflexivity.

    destruct a ; simpl in *|-*.
    assert(beq_nat (hole_var x) (hole_var v0) = false).
    assert(H1 := H0).
    apply VarSetProperties.add_mem_6 in H0.
    apply beq_nat_false_iff.
    unfold not ; intros ; unfold hole_var in *|-*.
    clear IHc H H1 ; omega.
    rewrite H1.
    rewrite IHc.
    rewrite MP.ssubst_bind with (f2 :=(fun v1 : T.expr =>
     cast_eapp
     (cast_eabs (cast_var (hole_var v0))
        (ssubst n ss (cast_var (hole_var x)) (fill c e) (phi v bs))) v1)).
    reflexivity.

    apply functional_extensionality.
    intros.
    rewrite MP.ssubst_eapp.
    rewrite MP.ssubst_eabs.
    assert(S.beq_var (hole_var x) (hole_var v0) = false).
    assumption.
    rewrite H2.
    reflexivity.
    apply VarSetProperties.add_mem_5 in H0.
    assumption.
  Qed.


End ContextProperties.

Module TranslationProperties (R:Replacement) 
    (T:StagedCalculus) (M:Monad R T) (MP:MonadProperties R T M). 

  Module Translation := MP.Translation.
  Module ContextProperties := ContextProperties R T M MP.
  Module StaticProperties := ContextProperties.TranslationStaticProperties.
  Module CalculusProperties := CalculusProperties R M.S.
  Module BindingSetProperties := BindingSetProperties R.
  Import StaticProperties.
  Import Translation.
  Import M.S.
  Import M.

  Lemma ssubst_fill_hole:
    forall (h:var) (e v:T.expr) (c:Context.t) (n:nat),
      VarSet.mem h (Context.context_hole_set c) = false ->
      ssubst n StageSet.empty (M.cast_var (hole_var h)) (Context.fill c e) v =
      Context.fill (Context.ssubst_context n StageSet.empty (hole_var h) c v) 
      (ssubst n StageSet.empty (M.cast_var (hole_var h)) e v).
  Proof.
    induction c ; intros ; simpl.
    reflexivity.
    destruct a.
    specialize (IHc n).
    simpl in H.
    assert(beq_nat (hole_var h) (hole_var v0) = false).
    apply VarSetProperties.add_mem_6 in H.
    apply beq_nat_false_iff.
    unfold not ; intros ; unfold hole_var in *|-*.
    clear IHc ; omega.
    rewrite H0.
    simpl.
    apply MP.ssubst_bind.
    apply functional_extensionality.
    intros.
    rewrite MP.ssubst_eapp.
    rewrite MP.ssubst_eabs.
    assert(beq_var (hole_var h) (hole_var v0) = false).
    assumption.
    rewrite H1.
    rewrite IHc.
    reflexivity.
    apply VarSetProperties.add_mem_5 in H.
    assumption.
  Qed.

(*
  Lemma ssubst_context_hole:
    forall (e:S.expr) (bs:list nat),
    let (_, cs) := trans e bs in
    forall (m n:nat) (h:var) (v:T.expr) (ss:StageSet.t),
    Context.ssubst_context m ss (hole_var h) (nth n cs nil) v = (nth n cs nil).
  Proof.
    admit.
  Qed.

  Lemma ssubst_fill_hole:
    forall (e:S.expr) (bs:list nat),
    let (_, cs) := trans e bs in
    forall (m n:nat) (h:var) (e v:T.expr) (ss:StageSet.t),
      ssubst m ss (M.cast_var (hole_var h)) (Context.fill (nth n cs nil) e) v =
      Context.fill (Context.ssubst_context m ss (hole_var h) (nth n cs nil) v) 
      (ssubst m ss (M.cast_var (hole_var h)) e v).
  Proof.
    intros.
    specialize (ssubst_context_hole e bs) ; intros.
    destruct (trans e) ; intros.
    specialize (H m n).
    induction (nth n t nil).
    reflexivity.

    simpl in *|-* ; destruct a.
    apply MP.ssubst_bind.
    apply functional_extensionality.
    intros.
    rewrite MP.ssubst_eapp.
    rewrite MP.ssubst_eabs.
    specialize (H h v (if beq_var (hole_var h) (hole_var v0) then StageSet.add m ss else ss)).
    inversion H ; simpl.
    
    rewrite H2.
    rewrite H2.
    rewrite IHc.
    

    simpl in H.
    assert(beq_nat (hole_var h) (hole_var v0) = false).
    apply VarSetProperties.add_mem_6 in H.
    apply beq_nat_false_iff.
    unfold not ; intros ; unfold hole_var in *|-*.
    clear IHc ; omega.
    rewrite H0.
    simpl.
    apply MP.ssubst_bind.
    apply functional_extensionality.
    intros.
    rewrite MP.ssubst_eapp.
    rewrite MP.ssubst_eabs.
    assert(beq_var (hole_var h) (hole_var v0) = false).
    assumption.
    rewrite H1.
    rewrite IHc.
    reflexivity.
    apply VarSetProperties.add_mem_5 in H.
    assumption.
  Qed.
*)

  Lemma ssubst_fill_source:
    forall (x:var) (e v:T.expr) (c:Context.t) (ss:StageSet.t) (n:nat),
      ssubst n ss (M.cast_var (source_var x)) (Context.fill c e) v =
      Context.fill (Context.ssubst_context n ss (source_var x) c v) 
      (ssubst n ss (M.cast_var (source_var x)) e v).
  Proof.
    assert(forall (m n:nat), beq_nat (source_var m) (hole_var n) = false).
    intros ; unfold source_var, hole_var ; apply beq_nat_false_iff ; omega.
    induction c ; intros ; simpl.
    reflexivity.
    destruct a.
    specialize (IHc ss n).
    apply MP.ssubst_bind.
    apply functional_extensionality.
    intros.
    rewrite MP.ssubst_eapp.
    rewrite MP.ssubst_eabs.
    rewrite H ; rewrite H.
    rewrite IHc.
    reflexivity.
  Qed.

  Lemma ssubst_app_source:
    forall (x:var) (v:T.expr) (c1 c2:Context.t) (ss:StageSet.t) (n:nat),
      Context.ssubst_context n ss (source_var x) (c1++c2) v =
      (Context.ssubst_context n ss (source_var x) c1 v) ++
      (Context.ssubst_context n ss (source_var x) c2 v).
  Proof.
    assert(forall (m n:nat), beq_nat (source_var m) (hole_var n) = false).
    intros ; unfold source_var, hole_var ; apply beq_nat_false_iff ; omega.
    induction c1 ; intros ; simpl in *|-*.
    reflexivity.
    destruct a.
    rewrite H.
    rewrite IHc1.
    reflexivity.
  Qed.

  Lemma ssubst_merge_source:
    forall (x:var) (v:T.expr) (cs1 cs2:Context.t_stack) (ss:StageSet.t) (n:nat),
      Context.ssubst_stack n ss (source_var x) (Context.merge cs1 cs2) v =
      Context.merge (Context.ssubst_stack n ss (source_var x) cs1 v) 
      (Context.ssubst_stack n ss (source_var x) cs2 v).
  Proof.
    induction cs1 ; intros ; simpl in *|-*.
    reflexivity.
    destruct cs2 ; simpl.
    reflexivity.
    simpl.
    rewrite ssubst_app_source.
    rewrite IHcs1.
    reflexivity.
  Qed.

  Lemma trans_ssubst_source: 
    forall (e v:expr) (bs:list nat) (x:var) (ss:StageSet.t) (n:nat), 
    let (e', cs) := trans e bs in
    svalue 0 v ->
    depth v = 0 ->
    length cs <= n ->
    StageSet.ub n ss = true ->
    trans (S.ssubst n ss x e v) bs =
    (M.ssubst n ss (cast_var (source_var x)) e' (phi v bs),
    Context.ssubst_stack (pred n) (StageSet.remove n ss) (source_var x) cs (phi v bs)).
  Proof.
    assert(forall (x v:nat), beq_nat x v = 
    beq_nat (source_var x) (source_var v)) as HSInject.
    intros ; unfold source_var ; remember (beq_nat x v) ; 
    destruct b ; symmetry in Heqb ; symmetry.
    apply beq_nat_true_iff in Heqb.
    subst ; rewrite <- beq_nat_refl ; reflexivity.
    apply beq_nat_false_iff ; apply beq_nat_false in Heqb.
    omega.

    induction e ; simpl ; intros.

    (* Case EConst *)
    rewrite MP.ssubst_ret.
    rewrite MP.ssubst_econst.
    reflexivity.
    
    (* Case EVar *)
    rewrite MP.ssubst_ret.
    rewrite MP.ssubst_evar.
    rewrite <- HSInject.
    destruct (beq_nat x v && CRaw.BindingSet.rho n ss).
    specialize (svalue_phi v0 bs H) ; intros.
    unfold trans_expr in H3.
    specialize (depth_length v0 bs) ; intros.
    rewrite H0 in H4.
    destruct (trans v0) ; subst.
    destruct t ; simpl in H4 ; [reflexivity|inversion H4].
    reflexivity.
    
    (* EAbs *)
    specialize (IHe v0 bs x).
    destruct (trans e) ; intros.
    rewrite MP.ssubst_ret.
    rewrite MP.ssubst_eabs.
    rewrite <- HSInject.
    destruct (beq_nat x v).
    rewrite IHe ; auto.
    rewrite StageSetProperties.remove_add_remove ; auto.
    rewrite <- StageSetProperties.ub_le_1 with (m:=n) ; auto.
    rewrite IHe ; auto.

    (* EFix *)
    specialize (IHe v1 bs x).
    destruct (trans e) ; intros.
    rewrite MP.ssubst_ret.
    rewrite MP.ssubst_efix.
    rewrite <- HSInject.
    rewrite <- HSInject.
    destruct (beq_nat x v || beq_nat x v0).
    rewrite IHe ; auto.
    rewrite StageSetProperties.remove_add_remove ; auto.
    rewrite <- StageSetProperties.ub_le_1 with (m:=n) ; auto.
    rewrite IHe ; auto.

    (* EApp *)
    specialize (IHe1 v (map_iter_booker e2 bs 0) x).
    specialize (IHe2 v bs x).
    destruct (trans e1) ; destruct (trans e2) ; intros.
    rewrite IHe2 ; auto ; clear IHe2.
    unfold map_iter_booker in *|-*.
    rewrite map_iter_ssubst ; auto.
    rewrite IHe1 ; auto ; clear IHe1.
    rewrite phi_depth_0 with (bs2:=nil) ; auto.
    rewrite phi_depth_0 with (bs1:=bs) (bs2:=nil) ; auto.
    rewrite ssubst_merge_source.
    rewrite MP.ssubst_bind with (f2:= fun v1 => bind 
      (ssubst n ss (cast_var (source_var x)) e0 (phi v nil))
      (fun v2 => cast_eapp v1 v2)).
    reflexivity.
    apply functional_extensionality ; intros.
    rewrite MP.ssubst_bind with (f2:=(fun v2 : T.expr =>
    cast_eapp (ssubst n ss (cast_var (source_var x)) x0 (phi v nil)) v2)).
    reflexivity.
    apply functional_extensionality ; intros.
    rewrite MP.ssubst_eapp.
    reflexivity.
    rewrite ContextStaticProperties.merge_length in H1.
    apply max_lub_iff in H1 ; destruct H1 ; assumption.
    rewrite ContextStaticProperties.merge_length in H1.
    apply max_lub_iff in H1 ; destruct H1 ; assumption.

    (* ELoc *)
    rewrite MP.ssubst_ret, MP.ssubst_eloc ; reflexivity.
    
    (* ERef *)
    specialize (IHe v bs x).
    destruct (trans e) ; intros.
    rewrite IHe ; auto.
    rewrite MP.ssubst_bind with (f2:=fun v0 => cast_eref v0).
    reflexivity.
    apply functional_extensionality ; intros.
    rewrite MP.ssubst_eref.
    reflexivity.
    
    (* EDeref *)
    specialize (IHe v bs x).
    destruct (trans e) ; intros.
    rewrite IHe ; auto.
    rewrite MP.ssubst_bind with (f2:=fun v0 => cast_ederef v0).
    reflexivity.
    apply functional_extensionality ; intros.
    rewrite MP.ssubst_ederef.
    reflexivity.

    (* EAssign *)
    specialize (IHe1 v (map_iter_booker e2 bs 0) x).
    specialize (IHe2 v bs x).
    destruct (trans e1) ; destruct (trans e2) ; intros.
    rewrite IHe2 ; auto ; clear IHe2.
    unfold map_iter_booker in *|-*.
    rewrite map_iter_ssubst ; auto.
    rewrite IHe1 ; auto ; clear IHe1.
    rewrite phi_depth_0 with (bs2:=nil) ; auto.
    rewrite phi_depth_0 with (bs1:=bs) (bs2:=nil) ; auto.
    rewrite ssubst_merge_source.
    rewrite MP.ssubst_bind with (f2:= fun v1 => bind 
      (ssubst n ss (cast_var (source_var x)) e0 (phi v nil))
      (fun v2 => cast_eassign v1 v2)).
    reflexivity.
    apply functional_extensionality ; intros.
    rewrite MP.ssubst_bind with (f2:=(fun v2 : T.expr =>
    cast_eassign (ssubst n ss (cast_var (source_var x)) x0 (phi v nil)) v2)).
    reflexivity.
    apply functional_extensionality ; intros.
    rewrite MP.ssubst_eassign.
    reflexivity.
    rewrite ContextStaticProperties.merge_length in H1.
    apply max_lub_iff in H1 ; destruct H1 ; assumption.
    rewrite ContextStaticProperties.merge_length in H1.
    apply max_lub_iff in H1 ; destruct H1 ; assumption.

    (* EBox *)
    specialize (IHe v (0::bs) x).
    destruct (trans e) ; intros.
    destruct t ; simpl in *|-* ; intros ;
    rewrite IHe ; auto ; simpl in *|-*.
    rewrite MP.ssubst_ret ; auto.
    rewrite MP.ssubst_ebox ; auto.
    rewrite phi_depth_0 with (bs2:=bs) ; auto.
    apply StageSetProperties.ub_le_2 with (m:=n) ; auto.
    rewrite ssubst_fill_source.
    rewrite phi_depth_0 with (bs2:=bs) ; auto.
    rewrite MP.ssubst_ret ; auto.
    rewrite MP.ssubst_ebox ; auto.
    assert(StageSet.remove (S n) ss = ss).
    apply StageSetProperties.remove_equal.
    remember(Sets.NatSet.MSetIntern.mem (S n) ss).
    destruct b ; symmetry in Heqb.
    exfalso ; apply StageSetProperties.ub_le_3 with (n:=n) in Heqb ; 
    [omega|auto].
    reflexivity.
    rewrite H3.
    reflexivity.
    omega.
    apply StageSetProperties.ub_le_2 with (m:=n) ; auto.

    (* EUnbox *)
    destruct (List2.hd_cons bs 0).
    specialize (IHe v l x).
    destruct (trans e) ; intros.
    rewrite IHe ; auto.
    rewrite MP.ssubst_eunbox ; auto.
    simpl.
    rewrite MP.ssubst_evar.
    assert(beq_nat (source_var x) (hole_var n0) &&
       CRaw.BindingSet.rho (pred n) (StageSet.remove n ss) = false).
    apply andb_false_iff ; left.
    apply beq_nat_false_iff.
    unfold source_var, hole_var ; omega.
    rewrite H3 ; clear H3.
    rewrite phi_depth_0 with (bs2:=bs) ; auto.
    simpl in H1 ; omega.
    rewrite <- StageSetProperties.ub_pred ; auto.

    (* ERun *)
    specialize (IHe v bs x).
    destruct (trans e) ; intros.
    rewrite IHe ; auto.
    rewrite MP.ssubst_bind with (f2:=fun v0 => cast_erun v0).
    reflexivity.
    apply functional_extensionality ; intros.
    rewrite MP.ssubst_erun.
    reflexivity.

    (* ELift *)
    specialize (IHe v bs x).
    destruct (trans e) ; intros.
    rewrite IHe ; auto.
    rewrite MP.ssubst_bind with (f2:=fun v0 => cast_elift v0).
    reflexivity.
    apply functional_extensionality ; intros.
    rewrite MP.ssubst_elift.
    reflexivity.
  Qed.

  Lemma context_mem_length_booker:
    forall (e:S.expr) (bs:list nat),
    let (_, cs) := trans e bs in
    forall (n:nat),
    length (nth n cs nil) = booker e n.
  Proof.
    induction e ; simpl ; intros ; 
    try(destruct n ; auto ; fail) ;

    try(specialize(IHe bs) ;
    destruct (trans e) ; intros ;
    apply IHe ; fail) ;

    try(specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ;
    destruct (trans e1) ; destruct (trans e2) ; intros ;
    rewrite ContextStaticProperties.merge_nth ;
    rewrite app_length ;
    rewrite IHe1, IHe2 ; reflexivity).

    specialize (IHe (0::bs)).
    destruct (trans e).
    destruct t ; intros ; simpl in *|-*.
    specialize (IHe (S n)) ; destruct n ; auto.
    specialize (IHe (S n)) ; simpl in *|-*.
    assumption.
    
    destruct (List2.hd_cons bs 0).
    specialize (IHe l).
    destruct (trans e) ; intros.
    simpl in *|-*.
    destruct n0 ; auto.
  Qed.

  Lemma context_mem_booker:
    forall (e:S.expr) (bs:list nat),
    let (_, cs) := trans e bs in
    forall (n:nat) (v:var),
    n < length bs ->
    VarSet.mem v (Context.context_hole_set (nth n cs nil)) = true ->
    nth n bs 0 <= v < (nth n bs 0) + (booker e n).
  Proof.
    induction e ; simpl ; intros ;
    
    try(destruct n ; inversion H0 ; fail) ;

    try(specialize (IHe bs) ;
    destruct (trans e) ; intros ;
    apply IHe ; auto ; fail) ;

    try(specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ; unfold map_iter_booker in *|-* ;
    destruct (trans e1) ; destruct (trans e2) ; intros ;
    rewrite ContextStaticProperties.merge_nth in H0 ;
    rewrite ContextStaticProperties.context_hole_set_app in H0 ;
    rewrite VarSetProperties.union_mem in H0 ;
    apply orb_true_iff in H0 ; destruct H0 ; [
    rewrite List2Properties.length_map_iter in IHe1 ;
    specialize (IHe1 n v H H0) ; clear IHe2 ;
    specialize(List2Properties.map_iter_nth_indep
    (fun b n => (b + booker e2 n)%nat) bs n 0 0 0 H) ; intros ;
    rewrite H1 in IHe1 ;
    destruct IHe1 ; split ; rewrite plus_0_r in H3 ; omega|
    clear IHe1 ; specialize (IHe2 n v H H0) ; omega]).

    specialize (IHe (0::bs)).
    destruct (trans e).
    destruct t ; simpl in *|-* ; intros.
    destruct n ; simpl in H0 ; inversion H0.
    apply lt_n_S in H.
    specialize (IHe (S n) v H H0) ; clear H H0 ; simpl in *|-*.
    assumption.
    
    destruct bs ; simpl in *|-*.
    specialize (IHe nil).
    destruct (trans e) ; intros.
    destruct n ; simpl in *|-*.
    rewrite <- VarSetProperties.singleton_equal_add in H0.
    rewrite VarSetProperties.singleton_mem in H0.
    subst ; omega.
    apply lt_S in H ; apply lt_S_n in H.
    specialize (IHe n v H H0) ; clear H H0.
    destruct n ; omega.

    specialize (IHe bs).
    destruct (trans e) ; intros ; simpl in *|-*.
    destruct n0 ; simpl in *|-*.
    rewrite <- VarSetProperties.singleton_equal_add in H0.
    rewrite VarSetProperties.singleton_mem in H0.
    subst ; omega.
    apply IHe ; auto.
    apply lt_S_n in H ; auto.
  Qed.
    
  Lemma context_mem:
    forall (e:S.expr) (bs:list nat),
    let (_, cs) := trans e bs in
    forall (n:nat),
    n < length bs ->
    match nth n cs nil with
    | nil => True
    | (e, v) :: c => VarSet.mem v (Context.context_hole_set c) = false
    end.
  Proof.
    induction e ; intros ; simpl in *|-* ; intros ;
    try(destruct n ; auto ; fail) ;

    try(specialize (IHe bs) ;
    destruct (trans e bs) ; intros ;
    specialize (IHe n H) ;
    assumption).

    (* EApp *)
    specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ;
    specialize (context_mem_booker e1 (map_iter_booker e2 bs 0)) ; 
    intros CMB1 ;
    specialize (context_mem_booker e2 bs) ; intros CMB2 ;
    destruct (trans e1) ; destruct (trans e2) ;
    intros ; specialize (IHe1 n) ; specialize (IHe2 n) ;
    rewrite ContextStaticProperties.merge_nth ;
    specialize (CMB1 n) ; specialize (CMB2 n) ;
    destruct (nth n t nil) ; simpl ; [
    apply IHe2 ; auto |].
    destruct p ;
    rewrite ContextStaticProperties.context_hole_set_app ;
    rewrite VarSetProperties.union_mem ;
    apply orb_false_iff ; 
    unfold map_iter_booker in *|-* ; split.
    rewrite List2Properties.length_map_iter in IHe1.
    apply IHe1 ; auto.
    rewrite List2Properties.length_map_iter in CMB1.
    remember (VarSet.mem v (Context.context_hole_set (nth n t0 nil))).
    symmetry in Heqb ; destruct b ; auto ; exfalso.
    apply CMB2 in Heqb ; auto ; clear CMB2.
    assert(VarSet.mem v (Context.context_hole_set ((e3, v) :: t1)) = true).
    simpl ; apply VarSetProperties.add_mem_3.
    specialize (CMB1 v H H0) ; clear H0 IHe2 IHe1 ;
    specialize(List2Properties.map_iter_nth_indep 
      (fun b n => (b + booker e2 n)%nat) bs n 0 0 0 H) ; intros ;
    rewrite plus_0_r in H0 ; rewrite H0 in CMB1 ; clear H0 ;
    omega.

    (* EAssign (same as EApp. Should deduplicate) *)
    specialize (IHe1 (map_iter_booker e2 bs 0)) ;
    specialize (IHe2 bs) ;
    specialize (context_mem_booker e1 (map_iter_booker e2 bs 0)) ; 
    intros CMB1 ;
    specialize (context_mem_booker e2 bs) ; intros CMB2 ;
    destruct (trans e1) ; destruct (trans e2) ;
    intros ; specialize (IHe1 n) ; specialize (IHe2 n) ;
    rewrite ContextStaticProperties.merge_nth ;
    specialize (CMB1 n) ; specialize (CMB2 n) ;
    destruct (nth n t nil) ; simpl ; [
    apply IHe2 ; auto |].
    destruct p ;
    rewrite ContextStaticProperties.context_hole_set_app ;
    rewrite VarSetProperties.union_mem ;
    apply orb_false_iff ; unfold map_iter_booker in *|-* ; split.
    rewrite List2Properties.length_map_iter in IHe1.
    apply IHe1 ; auto.
    rewrite List2Properties.length_map_iter in CMB1.
    remember (VarSet.mem v (Context.context_hole_set (nth n t0 nil))).
    symmetry in Heqb ; destruct b ; auto ; exfalso.
    apply CMB2 in Heqb ; auto ; clear CMB2.
    assert(VarSet.mem v (Context.context_hole_set ((e3, v) :: t1)) = true).
    simpl ; apply VarSetProperties.add_mem_3.
    specialize (CMB1 v H H0) ; clear H0 IHe2 IHe1 ;
    specialize(List2Properties.map_iter_nth_indep 
      (fun b n => (b + booker e2 n)%nat) bs n 0 0 0 H) ; intros ;
    rewrite plus_0_r in H0 ; rewrite H0 in CMB1 ; clear H0 ;
    omega.
    
    specialize (IHe (0 :: bs)).
    destruct (trans e) ; intros.
    destruct t ; simpl in *|-* ; intros.
    destruct n ; auto.
    specialize (IHe (S n)).
    apply IHe ; auto.
    apply lt_n_S ; auto.

    destruct bs ; simpl in *|-*.
    specialize (IHe nil).
    destruct (trans e nil) ; intros.
    simpl in *|-*.
    destruct n ; auto.
    apply IHe ; auto ; omega.

    specialize (IHe bs).
    destruct (trans e) ; intros.
    simpl in *|-*.
    destruct n0 ; auto.
    apply IHe ; auto.
    omega.
  Qed.

  Lemma trans_mem_length:
    forall (M:Memory.t) (bs:list nat), 
    length (trans_mem M bs) = length M.
  Proof.
    induction M ; simpl ; intros ; auto.
  Qed.

  Lemma trans_mem_fresh:
    forall (M:Memory.t) (bs:list nat), 
    T.Memory.fresh (trans_mem M bs) = Memory.fresh M.
  Proof.
    induction M ; simpl ; intros ; auto.
  Qed.

  Lemma trans_mem_set:
    forall (M:Memory.t) (l:CRaw.location) (bs:list nat) (v:S.expr),
    l <= length M ->
    trans_mem (CRaw.Memory.set l v M) bs =
    T.Memory.set l (phi v bs) (trans_mem M bs).
  Proof.
    induction M ; simpl ; intros.
    apply le_n_0_eq in H ; subst ; auto.
    destruct l ; simpl ; auto.
    apply le_S_n in H.
    rewrite IHM ; auto.
  Qed.

  Lemma trans_mem_get:
    forall (M:Memory.t) (l:CRaw.location) (bs:list nat),
    l < length M ->
    phi (CRaw.Memory.get l M) bs =
    T.Memory.get l (trans_mem M bs).
  Proof.
    induction M ; simpl ; intros.
    apply lt_n_O in H ; contradiction.
    destruct l ; simpl ; auto.
    apply lt_S_n in H.
    unfold CRaw.Memory.get, T.Memory.get ; simpl.
    specialize (IHM l bs H).
    unfold CRaw.Memory.get, T.Memory.get in IHM ; simpl in IHM.
    rewrite IHM ; auto.
  Qed.

  Definition ltb (m n:nat) := leb (S m) n.

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

  Inductive admin_context_ssubst (n:nat) (h:CRaw.var)
    (m:nat) (v:T.expr) (b1 b2:nat) : Context.t -> Context.t -> Prop :=
  | ACSubst_nil : admin_context_ssubst n h m v b1 b2 nil nil
  | ACSubst_cons : forall (u1 u2:T.expr) (c1 c2:Context.t),
      admin_ssubst n h m v b1 u1 u2 ->
      admin_context_ssubst n h m v b1 b2 c1 c2 ->
      admin_context_ssubst n h m v b1 b2
        (cons (u1,(b2+(length c1))%nat) c1) 
        (cons (u2,(b2+(length c1))%nat) c2).

  Inductive admin_stack_ssubst (n:nat) (h:CRaw.var) (v:T.expr) : 
    list nat -> nat -> Context.t_stack -> Context.t_stack -> Prop :=
  | ASSubst_nil : forall (bs:list nat) (b:nat), admin_stack_ssubst n h v bs b nil nil
  | ASSubst_cons_nil: forall (c1 c2:Context.t) (bs:list nat) (b1 b2:nat),
      admin_context_ssubst n h 0 v b1 b2 c1 c2 ->
      admin_stack_ssubst n h v (b1::bs) b2 (c1::nil) (c2::nil)
  | ASSubst_cons : forall (bs:list nat) (b1 b2:nat) (c1 c2 c1' c2':Context.t) (cs1 cs2:Context.t_stack),
      admin_context_ssubst n h (length c1') v b1 b2 c1 c2 ->
      admin_stack_ssubst (pred n) h v bs b1 (c1'::cs1) (c2'::cs2) ->
      admin_stack_ssubst n h v (b1::bs) b2 (c1::c1'::cs1) (c2::c2'::cs2).

  Lemma admin_fill_ssubst_1:
    forall (e:S.expr) (bs:list nat),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) in
    match cs with
    | c1 :: nil => 
      match c1 with
      | nil => False
      | (eh, h) :: c1' => let b := hd 0 bs in
        forall (v e2:T.expr) (c2:Context.t),
        admin_context_ssubst 0 h 0 v b 0 c1' c2 ->
        admin_ssubst 1 h (booker e 0) v 0 e1 e2 ->
        admin_ssubst 0 h (booker e 1) v b
        (Context.fill c1' (ret (cast_ebox e1))) (Context.fill c2 (ret (cast_ebox e2)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (context_stack_not_nil e (0::bs)) ; intros CSNotNil.
    specialize (length_h_match e (0::bs)) ; intros LengthHMatch.
    destruct (trans e (0 :: bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t ; auto.
    exfalso ; apply CSNotNil ; simpl ; auto.
    
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
    rewrite MP.ssubst_ret, MP.ssubst_ebox ; auto.
    repeat(constructor).
    apply H1 ; auto.
    simpl in *|-*.
    rewrite StageSetProperties.ub_le_2 with (m:=0) ; auto.
    destruct p ; subst ; intros.
    assert(Tmp4 := Tmp3).
    apply lt_le_weak in Tmp3.
    inversion H0 ; subst ; simpl.
    unfold admin_ssubst ; intros.
    simpl in *|-*.
    assert(~ ((e1, v) :: t = nil \/ False)) as Tmp2.
    unfold not ; clear ; intros ; destruct H ; auto ; inversion H.
    specialize (IHt Tmp2 Tmp3 v0 e2 c0 H6 H1).

    assert(beq_var (hole_var v) (hole_var (length t)) = false) as BeqFalse1.
    subst ; unfold hole_var ; apply beq_nat_false_iff ; 
    generalize Tmp4 ; clear ; intros ; omega.

    rewrite MP.ssubst_bind with (f2:= fun v2 =>
        (cast_eapp (cast_eabs (cast_var (hole_var (length t)))
         (ssubst 0 ss (cast_var (hole_var v)) 
           (Context.fill t (ret (cast_ebox e0))) v0)) v2)); auto.
    constructor ; auto ; intros.
    constructor ; [| constructor].
    constructor.
    apply IHt ; auto ; intros.
    apply functional_extensionality ; intros.
    rewrite MP.ssubst_eapp, MP.ssubst_eabs, BeqFalse1 ; auto.
  Qed.

  Lemma admin_fill_ssubst_2_strong:
    forall (e:S.expr) (bs:list nat),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) in
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
          (Context.fill c1 (ret (cast_ebox e1))) v) 
          (Context.fill c2 (ret (cast_ebox e2)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (depth_length e (0::bs)) ; intros DpthLength1.
    specialize (context_stack_not_nil e (0::bs)) ; intros CSNotNil.
    specialize (length_h_match e (0::bs)) ; intros LengthHMatch.
    specialize (booker_length e (0::bs)) ; intros BookerLength.
    destruct (trans e (0 :: bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t1 ; auto.
    destruct t0 ; auto.
    exfalso ; apply CSNotNil ; simpl ; auto.

    rewrite BookerLength ; simpl.
    clear LengthHMatch BookerLength CSNotNil.
    induction t.
    destruct p ; intros.
    inversion H2 ; subst ; simpl in *|-*.
    rewrite MP.ssubst_ret, MP.ssubst_ebox ; repeat(constructor) ; auto.

    simpl in *|-*.
    destruct p ; intros.
    inversion H2 ; subst ; simpl in *|-*.
    rewrite DpthLength1 in H ; destruct bs.
    exfalso ; generalize H ; clear ; simpl ; intros ; omega.
    specialize (IHt DpthLength1 v0 e2 c0) ; simpl in *|-*.
    case_beq_nat v (length t).
      rewrite MP.ssubst_bind with (f2:= fun v2 =>
        (cast_eapp (cast_eabs (cast_var (hole_var (length t)))
         (ssubst 1 (StageSet.add 1 ss) (cast_var (hole_var (length t))) 
           (Context.fill t (ret (cast_ebox e0))) v0)) v2)); auto.
      constructor ; auto ; intros.
      repeat(constructor).
      apply IHt ; auto.
      rewrite StageSetProperties.add_mem_4 ; auto.
      rewrite <- StageSetProperties.ub_le_1 ; auto.
      assert(ltb (length t) (S (length t)) = true).
      clear ; unfold ltb ; apply leb_iff ; omega.
      rewrite H4 in H3 ; clear H4.
      assert(ltb (length t) (length t) = false).
      clear ; unfold ltb ; apply leb_iff_conv ; omega.
      rewrite H4 ; clear H4 ; auto.
      apply functional_extensionality ; intros.
      rewrite MP.ssubst_eapp, MP.ssubst_eabs ; auto.
      rewrite <- beq_nat_refl ; auto.

      assert(ltb v (length t) = ltb v (S (length t))) as LtbEq.
      generalize E ; clear ; intros ; unfold ltb.
      remember (leb (S v) (S (length t))).
      destruct b ; symmetry in Heqb.
      apply leb_iff ; apply leb_iff in Heqb ; omega.
      apply leb_iff_conv ; apply leb_iff_conv in Heqb ; omega.
      rewrite LtbEq in IHt ; clear LtbEq.

      rewrite MP.ssubst_bind with (f2:= fun v2 =>
        (cast_eapp (cast_eabs (cast_var (hole_var (length t)))
         (ssubst 1 ss (cast_var (hole_var v)) 
           (Context.fill t (ret (cast_ebox e0))) v0)) v2)); auto.
      constructor ; auto ; intros.
      repeat(constructor).
      apply IHt ; auto.
      apply functional_extensionality ; intros.
      rewrite MP.ssubst_eapp, MP.ssubst_eabs ; auto.
      assert(beq_var (hole_var v) (hole_var (length t)) = false).
      generalize E ; clear ; intros ; unfold hole_var ; 
      apply beq_nat_false_iff ; omega.
      rewrite H4 ; auto.
  Qed.

  Lemma admin_fill_ssubst_2:
    forall (e:S.expr) (bs:list nat),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) in
    match cs with
    | c1 :: c1' :: nil => 
      match c1' with
      | nil => False
      | (eh, h) :: c1'' => let b := hd 0 bs in
        forall (v e2:T.expr) (c2:Context.t),
        admin_context_ssubst (pred (depth e)) h (length c1'') v b 0 c1 c2 ->
        admin_ssubst (depth e) h (booker e 0) v 0 e1 e2 ->
        admin_ssubst (pred (depth e)) h (booker e 1) v b
        (Context.fill c1 (ret (cast_ebox e1))) (Context.fill c2 (ret (cast_ebox e2)))
      end
    | _ => True
    end.
  Proof.
    intros.
    specialize (admin_fill_ssubst_2_strong e bs H) ; intros Strong.
    specialize (depth_length e (0::bs)) ; intros DpthLength1.
    specialize (booker_length e (0::bs)) ; intros BookerLength.
    destruct (trans e (0 :: bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t1 ; auto.
    destruct t0 ; auto.
    destruct p ; intros ; auto.
    rewrite DpthLength1 in *|-* ; simpl in *|-* ; auto.
    rewrite BookerLength in *|-* ; simpl in *|-* ; auto.
    unfold admin_ssubst ; simpl ; intros.
    apply Strong ; auto.
    apply H1 ; auto.
    rewrite StageSetProperties.ub_le_2 with (m:=1) ; auto.
  Qed.

  Lemma admin_fill_ssubst_3_strong:
    forall (e:S.expr) (bs:list nat),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) in
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
            (Context.fill c1 (ret (cast_ebox e1))) v) 
            (Context.fill c2 (ret (cast_ebox e2)))
	end
    | _ => True
    end.
  Proof.
    intros.
    specialize (depth_length e (0::bs)) ; intros DpthLength1.
    specialize (context_stack_not_nil e (0::bs)) ; intros CSNotNil.
    specialize (length_h_match e (0::bs)) ; intros LengthHMatch.
    specialize (booker_length e (0::bs)) ; intros BookerLength.
    destruct (trans e (0 :: bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t1 ; auto.
    specialize (context_shift_not_nil (t :: t0 :: t1 :: t2)) ; intros CShiftNotNil.
    destruct (Context.shift).
    destruct t3 ; auto.
    assert(length (t :: t0 :: t1 :: t2) > 0).
    simpl ; omega.
    specialize (CShiftNotNil H0 CSNotNil) ; destruct CShiftNotNil.
    apply H1 ; auto.

    rewrite BookerLength ; rewrite BookerLength ; simpl.
    clear LengthHMatch BookerLength CShiftNotNil CSNotNil.
    induction t.
    destruct p ; intros.
    inversion H2 ; subst ; rewrite DpthLength1 in *|-* ; simpl in *|-*.
    rewrite MP.ssubst_ret, MP.ssubst_ebox ; repeat(constructor) ; auto.

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
         destruct (ltb (length t) (n + length t0)) ; auto.
         apply StageSetProperties.add_add.
      rewrite MP.ssubst_bind with (f2:= fun v2 =>
        (cast_eapp (cast_eabs (cast_var (hole_var (length t)))
         (ssubst (S (S (length t2)))
         (if ltb (length t) (n + length t0) 
         then StageSet.add (S (length t2)) (StageSet.add (S (S (length t2))) ss) 
         else (StageSet.add (S (S (length t2))) ss))
           (cast_var (hole_var (length t))) 
           (Context.fill t (ret (cast_ebox e0))) v0)) v2)); auto.
      constructor ; auto ; intros.
      repeat(constructor).
      apply IHt ; auto.
      rewrite StageSetProperties.add_mem_4 ; auto.
      rewrite <- StageSetProperties.ub_le_1 ; auto.
      assert(ltb (length t) (S (length t)) = true).
      clear ; unfold ltb ; apply leb_iff ; omega.
      rewrite H4 in H3 ; clear H4.
      assert(ltb (length t) (length t) = false).
      clear ; unfold ltb ; apply leb_iff_conv ; omega.
      rewrite H4 ; clear H4 ; auto.
      rewrite <- Eq1 in H3 ; auto.
      apply functional_extensionality ; intros.
      rewrite MP.ssubst_eapp, MP.ssubst_eabs ; auto.
      rewrite <- beq_nat_refl ; auto.
      destruct (ltb (length t) (n + length t0)) ;
      auto ; rewrite Eq1 ; auto.

      assert(ltb v (length t) = ltb v (S (length t))) as LtbEq.
      generalize E ; clear ; intros ; unfold ltb.
      remember (leb (S v) (S (length t))).
      destruct b ; symmetry in Heqb.
      apply leb_iff ; apply leb_iff in Heqb ; omega.
      apply leb_iff_conv ; apply leb_iff_conv in Heqb ; omega.
      rewrite LtbEq in IHt ; clear LtbEq.

      rewrite MP.ssubst_bind with (f2:= fun v2 =>
        (cast_eapp (cast_eabs (cast_var (hole_var (length t)))
          (ssubst (S (S (length t2))) 
          (if ltb v (n + length t0) then StageSet.add (S (length t2)) ss else ss)
          (cast_var (hole_var v)) 
           (Context.fill t (ret (cast_ebox e0))) v0)) v2)); auto.
      constructor ; auto ; intros.
      repeat(constructor).
      apply IHt ; auto.
      apply functional_extensionality ; intros.
      rewrite MP.ssubst_eapp, MP.ssubst_eabs ; auto.
      assert(beq_var (hole_var v) (hole_var (length t)) = false).
      generalize E ; clear ; intros ; unfold hole_var ; 
      apply beq_nat_false_iff ; omega.
      rewrite H4 ; auto.
  Qed.

  Lemma admin_fill_ssubst_3:
    forall (e:S.expr) (bs:list nat),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) in
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
          (Context.fill c1 (ret (cast_ebox e1))) (Context.fill c2 (ret (cast_ebox e2)))
	end
    | _ => True
    end.
  Proof.
    intros.
    specialize (depth_length e (0::bs)) ; intros DpthLength1.
    specialize (admin_fill_ssubst_3_strong e bs H) ; intros Strong.
    destruct (trans e (0 :: bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t1 ; auto.
    destruct (Context.shift).
    destruct t3 ; auto.
    destruct p ; intros ; auto.
    rewrite DpthLength1 in *|-* ; simpl in *|-* ; auto.
    unfold admin_ssubst ; simpl ; intros.
    apply Strong ; auto.
    unfold admin_ssubst in H1 ; simpl in H1.
    apply H1 ; auto.
    destruct (ltb v (hd 0 bs + booker e 1)) ; auto.
    rewrite StageSetProperties.add_mem_4 ; auto.
    destruct (ltb v (hd 0 bs + booker e 1)) ; [
    rewrite <- StageSetProperties.ub_le_1 ; auto |] ;
    rewrite StageSetProperties.ub_le_2 with (m:=S (S (length t2))) ; auto.
  Qed.

  Lemma admin_fill_ssubst:
    forall (e:S.expr) (bs:list nat),
    depth e <= length (0 :: bs) ->
    let (e1, cs) := trans e (0 :: bs) in
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
        (Context.fill c1' (ret (cast_ebox e1))) (Context.fill c2 (ret (cast_ebox e2)))
      end
    | c1 :: c1' :: nil => 
      match c1' with
      | nil => False
      | (eh, h) :: c1'' => let b := hd 0 bs in
        forall (v e2:T.expr) (c2:Context.t),
        admin_context_ssubst (pred (depth e)) h (length c1'') v b 0 c1 c2 ->
        admin_ssubst (depth e) h (booker e 0) v 0 e1 e2 ->
        admin_ssubst (pred (depth e)) h (booker e 1) v b
        (Context.fill c1 (ret (cast_ebox e1))) (Context.fill c2 (ret (cast_ebox e2)))
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
          (Context.fill c1 (ret (cast_ebox e1))) (Context.fill c2 (ret (cast_ebox e2)))
	end
    end.
  Proof.
    intros.
    specialize (admin_fill_ssubst_1 e bs) ; intros Case1.
    specialize (admin_fill_ssubst_2 e bs) ; intros Case2.
    specialize (admin_fill_ssubst_3 e bs) ; intros Case3.
    destruct (trans e (0 :: bs)).
    destruct t ; auto.
    destruct t0 ; auto.
    destruct t ; auto.
    destruct p ; intros ; auto.
    destruct t1 ; auto.
    destruct t0 ; auto.
    destruct p ; intros ; auto.
    destruct (Context.shift) ; auto.
    destruct t3 ; auto.
    destruct p ; intros ; auto.
  Qed.

  Lemma sstep_rstep:
    forall (e1:S.expr) (bs:list nat) (e2:S.expr) (M1 M2:S.Memory.t),
    S.memory_svalue 0 M1 ->
    S.memory_depth M1 = 0 ->
    let n := depth e1 in
    n <= length bs ->
    S.sstep n (M1, e1) (M2, e2) -> 
    let (e1', cs1) := trans e1 bs in
    match cs1 with
    | nil => rstep (trans_mem M1 bs, e1') (trans_mem M2 bs, trans_expr e2 bs)
    | cs1 => let (c1, cs1') := Context.shift cs1 in
      match c1 with
      | nil => False
      | cons (t_eh, h) c1' => 
          let (e2', cs2) := trans e2 bs in
          let M1' := trans_mem M1 bs in
          let M2' := trans_mem M2 bs in
          exists eh, t_eh = trans_expr eh (0::nil) /\
          (
            S.svalue 0 eh /\ 
            M1 = M2 /\
            match c1' with
            | nil => admin_stack_ssubst (pred n) h (phi eh (0::nil)) 
                       (List.tl bs) (List.hd 0 bs) cs1' cs2
            | _ =>   admin_stack_ssubst (pred n) h (phi eh (0::nil))
                       (List.tl bs) (List.hd 0 bs) (Context.unshift cs1' c1') cs2
            end /\
            admin_ssubst n h (booker e1 0) (phi eh (0::nil)) (nth 0 bs 0) e1' e2'
          \/ 
            exists eh', let t_eh' := trans_expr eh' (0::nil) in
            rstep (M1', t_eh) (M2', t_eh') /\
            e1' = e2' /\
            cs2 = Context.unshift cs1' ((t_eh', h) :: c1')
          )
      end
    end.
  Proof.
    induction e1 ; simpl ; 
    intros bs e2 M1 M2 MemSvalue0 MemDepth0 BSLength Step ; intros.

    (* Case EConst *)
    inversion Step.

    (* Case EVar *)
    inversion Step.

    (* Case EAbs *)
    inversion Step ; subst.
    rewrite <- H in IHe1, BSLength.
    specialize (IHe1 bs e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
    specialize (depth_length e1 bs) ; intros.
    destruct (trans e1).
    rewrite <- H in H0.
    destruct t ; simpl in H0 ; inversion H0 ; subst.
    destruct (Context.shift (t :: t0)).
    destruct t1 ; simpl in *|-* ; auto.
    destruct p ; destruct (trans e3) ; intros.
    destruct IHe1 ; exists x.
    destruct H2 ; split ; [assumption|].
    destruct H3 ; [left | right] ; destruct H3.

      (* Case svalue *)
      destruct H4 ; destruct H5 ; subst.
      repeat(split ; auto).
      unfold admin_ssubst ; intros.
      assert(beq_var (hole_var v0) (source_var v) = false).
      clear ; unfold hole_var, source_var ; apply beq_nat_false_iff ; omega.
      destruct t0 ; simpl in *|-*.
      rewrite MP.ssubst_ret, MP.ssubst_eabs.
      repeat(constructor).
      apply H6.
      rewrite H7 ; assumption.
      rewrite H7 ; assumption.
      unfold admin_ssubst in H6.
      destruct (ltb v0 (nth 0 bs 0 + booker e1 0)) ;
      rewrite MP.ssubst_ret, MP.ssubst_eabs ;
      repeat(constructor) ;
      rewrite H7 ;
      apply H6 ; auto.

      (* Case not svalue *)
      exists x0.
      destruct H3 ; destruct H4 ; subst.
      auto.

    (* Case EFix *)
    inversion Step ; subst.
    rewrite <- H in IHe1, BSLength.
    specialize (IHe1 bs e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
    specialize (depth_length e1 bs) ; intros.
    destruct (trans e1).
    rewrite <- H in H0.
    destruct t ; simpl in H0 ; inversion H0 ; subst.
    destruct (Context.shift (t :: t0)).
    destruct t1 ; simpl in *|-* ; auto.
    destruct p ; destruct (trans e3) ; intros.
    destruct IHe1 ; exists x.
    destruct H2 ; split ; [assumption|].
    destruct H3 ; [left | right] ; destruct H3.
    
      (* Case svalue *)
      destruct H4 ; destruct H5 ; subst.
      repeat(split ; auto).
      intros.
      unfold admin_ssubst ; intros.
      assert(beq_var (hole_var v1) (source_var v)
               || beq_var (hole_var v1) (source_var v0) = false).
      clear ; unfold hole_var, source_var ;
      apply orb_false_iff ; split ; apply beq_nat_false_iff ; omega.
      destruct t0 ; simpl in *|-*.
      rewrite MP.ssubst_ret, MP.ssubst_efix.
      repeat(constructor).
      apply H6.
      rewrite H7 ; assumption.
      rewrite H7 ; assumption.
      unfold admin_ssubst in H6.
      destruct (ltb v0 (nth 0 bs 0 + booker e1 0)) ;
      rewrite MP.ssubst_ret, MP.ssubst_efix ;
      repeat(constructor) ;
      rewrite H7 ;
      apply H6 ; auto.

      (* Case not svalue *)
      exists x0.
      destruct H3 ; destruct H4 ; subst ; auto.

    (* Case EApp *)
    admit.
    (*
    inversion Step ; subst ; simpl in *|-*.
    
      (* Case EApp e1 e2,  e1 -> e1' *)
      admit.

      (* Case EApp e1 e2,  e2 -> e2' *)
      admit.

      (* Case EApp (EAbs), n = 0 *)
      symmetry in H ; apply max_0 in H.
      destruct H.
      clear IHe1_2 IHe1_1.
      specialize (depth_length e (List2.map_iter (fun b n => (b + booker e1_2 n)%nat) bs 0)) ; intros.
      assert(let (e0, _) := trans e (List2.map_iter (fun b n => (b + booker e1_2 n)%nat) bs 0) in
      cast_eabs (cast_var (source_var x)) e0 = 
      phi (CRaw.EAbs x e) (List2.map_iter (fun b n => (b + booker e1_2 n)%nat) bs 0)).
      simpl ; destruct (trans e) ; reflexivity.
      destruct (trans e).
      rewrite H3.
      rewrite H in H2 ; destruct t ; simpl in *|- ;
      [clear H2 |inversion H2].
      specialize (depth_length e1_2 bs) ; intros.
      specialize (svalue_phi e1_2 bs H1) ; intros.
      unfold trans_expr in H4.
      destruct (trans e1_2).
      rewrite H0 in H2 ; destruct t ; simpl in *|-;
      [clear H2 |inversion H2].
      rewrite H4 ; unfold Context.merge.
      apply Rel_step with 
      (e1:=trans_expr (S.ssubst 0 StageSet.empty x e e1_2) bs).
      apply MP.astep_bind_2 ; [constructor|].
      apply MP.astep_bind_2 ; [assumption|].
      specialize (trans_ssubst_source e e1_2 bs x StageSet.empty 0) ; intros.
      unfold trans_expr ; simpl.
      rewrite trans_depth_0 with (bs2:=bs) ; auto.
      specialize (depth_length e bs) ; intros.
      destruct (trans e bs).
      rewrite H2 ; auto ; clear H2.
      apply MP.astep_app_abs ; auto.
      omega.
      constructor.

      (* Case EApp (EFix), n = 0 *)
      admit.
    *)

    (* Case ELoc *)
    inversion Step.

    (* Case ERef *)
    specialize (depth_length e1 bs) ; intros DpthLength.
    inversion Step ; subst.
    specialize (IHe1 bs).
    destruct (trans e1).
    destruct t ; intros.

      (* SubCase ERef, n=0, e -> e' *)
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      unfold trans_expr in *|-* ; simpl in *|-*.
      inversion IHe1 ; subst.
      apply Rel_step with (e1:=bind e0 (fun v => cast_eref v)) ; auto.
      apply MP.astep_bind_eref ; assumption.
      destruct (trans e3).
      constructor ; [auto | intros ; constructor].

      (* SubCase ERef, n>0 *)
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      destruct (Context.shift (t :: t0)).
      destruct t1 ; simpl in *|-* ; auto.
      destruct p ; destruct (trans e3) ; intros.
      destruct IHe1 ; exists x.
      destruct H ; split ; [assumption|].
      destruct H0 ; [left | right] ; destruct H0.

        (* Case svalue *)
        destruct H2 ; destruct H3 ; subst.
        repeat(split ; auto).
        unfold admin_ssubst ; intros.
        rewrite MP.ssubst_bind with (f2:=fun v0 => cast_eref v0).
        constructor ; auto.
        intros ; constructor.
        apply functional_extensionality ; intros.
        rewrite MP.ssubst_eref ; auto.

        (* Case not svalue *)
        exists x0.
        destruct H0 ; destruct H2 ; subst ; auto.

      (* SubCase ERef, n=0, svalue 0 e *)
      specialize (svalue_phi e1 bs H1) ; intros SValuePhi.
      unfold trans_expr in SValuePhi.
      destruct (trans e1 bs).
      rewrite <- H in DpthLength ; destruct t ; [|inversion DpthLength].
      unfold trans_expr in *|-* ; clear IHe1 ; subst.
      apply Rel_step with (e1:=ret (cast_eloc (CRaw.Memory.fresh M1))).
      apply MP.astep_bind_2 ; auto.
      rewrite trans_mem_set ; auto.
      rewrite <- trans_mem_fresh with (bs:=bs) ; auto.
      apply MP.astep_eref ; auto.
      simpl ; constructor.

    (* Case EDeref *)
    specialize (depth_length e1 bs) ; intros DpthLength.
    inversion Step ; subst.
    specialize (IHe1 bs).
    destruct (trans e1).
    destruct t ; intros.

      (* SubCase EDeref, n=0, e -> e' *)
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      unfold trans_expr in *|-* ; simpl in *|-*.
      inversion IHe1 ; subst.
      apply Rel_step with (e1:=bind e0 (fun v => cast_ederef v)) ; auto.
      apply MP.astep_bind_ederef ; assumption.
      destruct (trans e3).
      constructor ; [auto | intros ; constructor].

      (* SubCase EDeref, n>0 *)
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      destruct (Context.shift (t :: t0)).
      destruct t1 ; simpl in *|-* ; auto.
      destruct p ; destruct (trans e3) ; intros.
      destruct IHe1 ; exists x.
      destruct H ; split ; [assumption|].
      destruct H0 ; [left | right] ; destruct H0.

        (* Case svalue *)
        destruct H2 ; destruct H3 ; subst.
        repeat(split ; auto).
        unfold admin_ssubst ; intros.
        rewrite MP.ssubst_bind with (f2:=fun v0 => cast_ederef v0).
        constructor ; auto.
        intros ; constructor.
        apply functional_extensionality ; intros.
        rewrite MP.ssubst_ederef ; auto.

        (* Case not svalue *)
        exists x0.
        destruct H0 ; destruct H2 ; subst ; auto.

      (* SubCase EDeref, n=0, svalue 0 e *)
      simpl.
      apply Rel_step with (e1:=trans_expr (CRaw.Memory.get l M2) bs).
      assert(phi (CRaw.ELoc l) bs = (cast_eloc l)) as Phi1.
      reflexivity.
      rewrite <- Phi1.
      apply MP.astep_bind_2 ; [constructor | simpl].
      rewrite svalue_phi.
      rewrite trans_mem_get ; auto.
      apply MP.astep_ederef ; auto.
      rewrite trans_mem_length ; auto.
      apply CalculusProperties.memory_svalue_get ; auto.
      simpl ; constructor.

    (* Case EAssign *)
    admit.

    (* Case EBox *)
    specialize (IHe1 (0::bs)).
    specialize (length_svalue e1 (0::bs) 0) ; intros LthSvalue.
    specialize (context_stack_not_nil e1 (0::bs)) ; intros CSNotNil.
    specialize (depth_length e1 (0::bs)) ; intros DpthLength.
    specialize (context_mem e1 (0::bs)) ; intros CMem1.
    specialize (admin_fill_ssubst e1 bs) ; intros FillSubst.
    specialize (booker_length e1 (0::bs)) ; intros BKLength1.
    inversion Step ; subst ; simpl in *|-*.
    destruct (trans e1).
    specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0).
    destruct t ; simpl in *|-* ; intros.

      (* Case of svalue 1 e1. Impossible *)
      rewrite DpthLength in H1 ; simpl in *|-* ; exfalso.
      apply CalculusProperties.svalue_not_sprogresses in H1 ; auto.
      apply LthSvalue ; auto.

      (* Case of stack > 0 *)
      destruct t0.

        (* Case of length(stack) = 1 *)
        rewrite DpthLength in *|-* ; simpl in *|-*.
        apply le_n_S in BSLength.
        specialize (IHe1 BSLength H1).
        destruct t.

          (* Case stack = [[]] Impossible *)
          contradiction.
   
          (* Case stack = [a :: lst] *)
          destruct p.
          unfold trans_expr ; simpl in *|-*.
          specialize (depth_length e3 (0::bs)) ; intros DpthLength2.
          destruct (trans e3) ; intros.
          destruct IHe1 ; destruct H.
          destruct H0.

            (* Case svalue *)
            destruct H0 ; destruct H2 ; 
            destruct H3 ; subst.
            destruct t.

            inversion H3 ; subst.
            rewrite svalue_phi ; auto.
            simpl.
            apply Rel_step with (e1:=
              (M.ssubst 0 StageSet.empty (M.cast_var (hole_var v)) 
                (M.ret (M.cast_ebox e)) (phi x (0 :: nil)))).
            apply MP.astep_bind_2 ; auto.
            apply MP.astep_app_abs ; auto.
            rewrite MP.ssubst_ret, MP.ssubst_ebox ; repeat(constructor).
            apply H4 ; auto.

            inversion H3 ; subst.
            inversion H6 ; subst.
            simpl in *|-*.
            rewrite svalue_phi ; auto.
            apply Rel_step with (e1:=
              M.ssubst 0 StageSet.empty (M.cast_var (hole_var v)) 
                (bind u1 (fun v1 => cast_eapp
                  (cast_eabs (cast_var (hole_var (length t)))
                  (Context.fill t (ret (cast_ebox e))))
                  v1)) (phi x (0 :: nil))).
            apply MP.astep_bind_2 ; auto.
            apply MP.astep_app_abs ; auto.
            assert(1 <= S (S (length bs0))) as Tmp1.
            clear ; omega.
            specialize (FillSubst Tmp1 
              (phi x (0 :: nil)) e2 ((u2,(length t)%nat)::c0) H6 H4).
            apply FillSubst ; auto.

            (* Case not svalue *)
            destruct H0 ; destruct H0 ; 
            destruct H2 ; subst.
            inversion H0 ; subst.
            apply Rel_step with (e1:=bind e0 (fun v0 =>
               cast_eapp
               (cast_eabs (cast_var (hole_var v))
               (Context.fill t (ret (cast_ebox e2)))) v0)).
            apply MP.astep_bind_app_eabs.
            rewrite trans_memory_depth_0 with (bs2:=0::bs) ; auto.
            rewrite trans_memory_depth_0 with (bs1:=bs) (bs2:=0::bs).
            assumption.
            rewrite <- DpthLength in H1.
            apply CalculusProperties.depth_sstep_2 in H1 ; auto.
            destruct H1 ; assumption.
            simpl ; constructor ;
            [assumption | intros ; constructor].

        (* Case of length(stack) > 1 *)
        rewrite DpthLength in H1, BSLength.
        simpl in H1, DpthLength, BSLength.
        rewrite <- DpthLength in H1.
        apply le_n_S in BSLength.
        rewrite <- DpthLength in BSLength.
        specialize (IHe1 BSLength H1).
        assert(length (t0 :: t1) > 0) as Tmp1.
        simpl ; clear IHe1 LthSvalue ; omega.
        assert(~ In nil (t0 :: t1)) as Tmp2.
        unfold not ; intros ; apply CSNotNil.
        right ; auto.
        specialize (context_shift_not_nil (t0::t1) Tmp1 Tmp2) ; 
        intros CSShiftNotNil ; clear Tmp1 Tmp2.
        assert(Context.shift (t0 :: t1) = Context.shift ((fun x => x) (t0 :: t1))) as Shift1.
        reflexivity.
        destruct (Context.shift (t0 :: t1)).
        destruct CSShiftNotNil.
        destruct t2 ; [exfalso ; auto |].
        destruct p ; destruct (trans e3) ; intros.
        destruct IHe1.
        destruct H2.
        destruct H3 ; subst.

          (* Case svalue *)
          destruct H3 ; subst.
          destruct H3 ; destruct H3 ; subst.
          destruct H4.
          destruct t2 ; simpl in *|-*.

          inversion H3 ; subst.
          exists x ; split ; auto ; left.
          repeat(split; auto) ; simpl.
          constructor.
          destruct t1 ; [|destruct (Context.shift (t1 :: t2))] ; 
          inversion Shift1 ; subst.
          rewrite DpthLength in *|-* ; simpl in *|-*.
          apply FillSubst ; simpl ; auto.
         
          exists x ; split ; auto ; left.
          repeat(split; auto) ; simpl.
          destruct t1 ; [ | destruct (Context.shift (t1 :: t2))] ; 
          inversion Shift1 ; subst.

          apply FillSubst ; auto.
          
          inversion H3 ; subst.
          destruct t3 ; simpl in H9 ; inversion H9.

          exists x ; split ; auto ; left.
          repeat(split; auto) ; simpl.
          destruct t1 ; [ inversion Shift1 ; subst ;
          simpl in H6 ; inversion H6|] ; subst.
          apply FillSubst ; simpl ; auto.
          destruct (Context.shift (t1 :: t4)) ; inversion Shift1 ; subst.
          simpl in H6 ; inversion H6 ; subst ; auto.
          simpl in *|-*.

          (* Case not svalue *)
          destruct H3 ; destruct H2 ; destruct H3 ; subst.
          exists x ; split ; auto ; right.
          exists x0.
          repeat(split ; auto).
          rewrite trans_memory_depth_0 with (bs2:=0::bs) ; auto.
          rewrite trans_memory_depth_0 with (bs1:=bs) (bs2:=0::bs) ; auto.
          apply CalculusProperties.depth_sstep_2 in H1 ; auto.
          destruct H1 ; assumption.

    (* Case EUnbox *)
    destruct bs ; [inversion BSLength|] ; simpl.
    specialize (depth_length e1 bs) ; intros DpthLength1.
    specialize (length_h e1 bs) ; intros LengthH.
    specialize (length_h_match e1 bs) ; intros LengthHMatch.
    specialize (booker_length e1 bs) ; intros BKLength1.
    specialize (IHe1 bs).
    assert(trans e1 bs = trans e1 ((fun x => x) bs)) as TransE1.
    reflexivity.
    destruct (trans e1 bs).
    inversion Step ; subst.

      (* Case EUnbox -> EUnbox *)
      apply le_S_n in BSLength.
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      specialize (depth_length e3 bs) ; intros DpthLength2.
      specialize (CalculusProperties.depth_sstep_2 M1 e1 M2 e3 MemDepth0 H1) ; 
      intros DpthStep ; simpl.
      destruct t.

        (* Case n = 1 *)
        unfold trans_expr in *|-* ; simpl in *|-*.
        assert(trans e3 bs = trans e3 ((fun x => x) bs)) as TransE3.
        reflexivity.
        destruct (trans e3 bs).
        exists e1.
        rewrite trans_depth_0 with (bs2:=bs) ; auto.
        rewrite <- TransE1.
        split ; auto.
        right.
        exists e3.
        destruct DpthStep.
        rewrite DpthLength1 in H ; apply le_n_0_eq in H.
        rewrite trans_depth_0 with (bs2:=bs) ; auto.
        rewrite <- TransE3.
        rewrite trans_memory_depth_0 with (bs2:=bs) ; auto.
        rewrite trans_memory_depth_0 with (bs1:=n::bs) (bs2:=bs) ; auto.
        repeat(split ; auto).
        rewrite <- H in DpthLength2 ; destruct t ; 
        inversion DpthLength2 ; auto.

        (* Case n > 1 *)
        assert(Context.shift (t :: t0) = Context.shift ((fun x => x) (t :: t0))) as Shift1.
        reflexivity.
        destruct (Context.shift (t :: t0)).
        destruct t1 ; simpl in *|-*.
        assumption.
        assert(trans e3 bs = trans e3 ((fun x => x) bs)) as TransE3.
        reflexivity.
        destruct p ; destruct (trans e3 bs).
        destruct IHe1.
        exists x.
        destruct H ; split ; auto.
        destruct H0 ; [left | right] ; destruct H0.

          (* Case svalue *)
          destruct H2 ; destruct H3.
          repeat(split ; auto).
          destruct bs.
          rewrite DpthLength1 in BSLength ; inversion BSLength.
          destruct t1.
          destruct t2 ; simpl in *|-* ; inversion H3 ; subst ;
          constructor ; rewrite BKLength1 in H4 ; simpl in H4.
          assert(forall e:T.expr, (e,n) = (e, n + (length (tl (0::nil)))))%nat as Tmp1.
          simpl ; rewrite plus_0_r ; reflexivity.
          simpl tl in Tmp1.
          rewrite Tmp1.
          rewrite Tmp1.
          apply ACSubst_cons with (u1:=e) (u2:=e2) (c1:=nil)  
            (c2:=nil) (n:=depth e1) (v:=(phi x (0 :: nil)))
            (b1:=n0) (b2:=n) ; auto.
          unfold admin_ssubst ; intros ; simpl.
          rewrite DpthLength1 ; simpl.
          rewrite DpthLength1 in H4 ; simpl in H4.
          unfold admin_ssubst in H4 ; simpl in H4.
          destruct t0.
          simpl in *|-*.
          apply H4 ; auto.
          rewrite DpthLength1 in H2 ; simpl in H2 ; auto.
          simpl in *|-*.
          destruct t1.
          inversion Shift1.
          destruct (Context.shift (t1 :: t2)).
          inversion Shift1.
          constructor.

          destruct t0.
          inversion Shift1 ; subst.
          destruct (Context.shift (t0 :: t2)) ; inversion Shift1 ; subst.
          assert(forall e:T.expr, (e,n) = (e, n + (length (tl (0::nil)))))%nat as Tmp1.
          simpl ; rewrite plus_0_r ; reflexivity.
          simpl tl in Tmp1.
          rewrite Tmp1.
          rewrite Tmp1.
          apply ACSubst_cons with (u1:=e) (u2:=e2) (c1:=nil)  
            (c2:=nil) (n:=depth e1) (v:=(phi x (0 :: nil)))
            (b1:=n0) (b2:=n) ; auto.
          constructor ; assumption.

          destruct t0.
          inversion Shift1 ; subst.
          simpl in *|-* ; inversion H3.
          constructor ; auto.
          admit.
          constructor ; auto.

          assert(Context.unshift t2 (p :: t1) = Context.unshift t2 ((fun x => x) (p :: t1))) as Shift2.
          reflexivity.
          destruct (Context.unshift t2 (p :: t1)).
          destruct t2 ; simpl in Shift2 ; inversion Shift2.
          inversion H3 ; subst.
          constructor ; auto.
          assert(forall e:T.expr, (e,n) = (e, n + (length (tl (0::nil)))))%nat as Tmp1.
          simpl ; rewrite plus_0_r ; reflexivity.
          simpl tl in Tmp1.
          rewrite Tmp1.
          rewrite Tmp1.
          
          apply ACSubst_cons with (u1:=e) (u2:=e2) (c1:=nil)  
            (c2:=nil) (n:=depth e1) (v:=(phi x (0 :: nil)))
            (b1:=n0) (b2:=n) ; auto.
          rewrite BKLength1 in H4.
          simpl in *|-*.
          rewrite DpthLength1 in H4. 
          rewrite DpthLength1 ; 
          unfold admin_ssubst in H4 ; unfold admin_ssubst ; intros ;
          simpl in *|-*.
          destruct t0 ; simpl in *|-*.
          apply H4 ; auto.
          assert(t4 = t).
          destruct t3 ; simpl.
          inversion Shift1 ; subst.
          simpl in Shift2 ; inversion Shift2 ; auto.
          destruct (Context.shift (t3 :: t5)).
          inversion Shift1 ; subst.
          simpl in Shift2 ; inversion Shift2 ; auto.
          subst.
          auto.
          constructor ; auto.

          constructor ; auto.
          assert(forall e:T.expr, (e,n) = (e, n + (length (tl (0::nil)))))%nat as Tmp1.
          simpl ; rewrite plus_0_r ; reflexivity.
          simpl tl in Tmp1.
          rewrite Tmp1.
          rewrite Tmp1.
          
          apply ACSubst_cons with (u1:=e) (u2:=e2) (c1:=nil)  
            (c2:=nil) (n:=depth e1) (v:=(phi x (0 :: nil)))
            (b1:=n0) (b2:=n) ; auto.
          rewrite BKLength1 in H4.
          simpl in *|-*.
          assert(t4 = t).
          destruct t0 ; simpl.
          inversion Shift1 ; subst.
          simpl in Shift2 ; inversion Shift2 ; auto.
          destruct (Context.shift (t0 :: t3)).
          inversion Shift1 ; subst.
          simpl in Shift2 ; inversion Shift2 ; auto.
          subst.
          assumption.
          constructor.


          unfold admin_ssubst ; intros.
          rewrite DpthLength1.
          rewrite MP.ssubst_eunbox.
          simpl.
          rewrite MP.ssubst_evar.
          case_beq_nat v n.
          rewrite <- beq_nat_refl.
          assert(ltb n (n+1) = true).
          clear ; unfold ltb ;
          apply leb_iff ; omega.
          rewrite H7, andb_true_l.
          rewrite BindingSetProperties.rho_false_mem ; auto.
          constructor.
          rewrite StageSetProperties.remove_mem_1 ; auto.
          apply StageSetProperties.add_mem_3.
          assert(beq_nat (hole_var v) (hole_var n) = false).
          apply beq_nat_false_iff ; unfold hole_var ; omega.
          rewrite H7, andb_false_l.
          constructor.

          (* Case not svalue *)
          exists x0.
          destruct H0 ; destruct H2 ; subst ; auto.
          repeat(split ; auto).
          rewrite trans_memory_depth_0 with (bs2:=bs) ; auto.
          destruct DpthStep.
          rewrite trans_memory_depth_0 with (bs1:=n::bs) (bs2:=bs) ; auto.

      (* Case EUnbox Box e -> e *)
      rewrite <- H in DpthLength1.
      destruct t ; [| inversion DpthLength1] ; simpl in *|-*.
      specialize (CalculusProperties.depth_svalue e2 0) ; intros.
      destruct H0 ; specialize (H2 H1).
      apply le_S_n, le_n_0_eq in H2.
      rewrite trans_depth_0 with (bs2:=0::bs) ; auto.
      specialize (depth_length e2 (0::bs)) ; intros DpthLength3.
      assert(trans e2 (0::bs) = trans e2 ((fun x => x) (0::bs))) as TransE3.
      reflexivity.
      assert((let (e8, _) := trans e2 (0::bs) in e8) = trans_expr e2 (0::bs)) as TransExpr.
      unfold trans_expr ; reflexivity.
      destruct (trans e2 (0::bs)).
      rewrite <- H2 in DpthLength3 ; destruct t ; [|inversion DpthLength3].
      exists (CRaw.EBox e2).
      unfold trans_expr ; simpl.
      rewrite trans_depth_0 with (bs2:=0::bs) ; auto.
      rewrite <- TransE3.
      inversion TransE1 ; subst.
      split ; auto ; left.
      repeat(split ; auto).
      constructor ; auto.
      constructor.

      unfold admin_ssubst ; intros.
      rewrite MP.ssubst_eunbox.
      rewrite MP.ssubst_evar.
      rewrite <- beq_nat_refl, andb_true_l ; simpl.
      rewrite BindingSetProperties.rho_O_true ; auto.
      constructor.
      apply H1.
      rewrite StageSetProperties.remove_mem_3 ; auto.
      specialize (StageSetProperties.ub_pred ss 1) ; intros.
      simpl in H5 ; rewrite H4 in H5 ; symmetry in H5 ; auto.

    (* Case ERun *)
    specialize (depth_length e1 bs) ; intros DpthLength.
    inversion Step ; subst.
    specialize (IHe1 bs).
    destruct (trans e1).
    destruct t ; intros.

      (* SubCase ERun, n=0, e -> e' *)
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      unfold trans_expr in *|-* ; simpl in *|-*.
      inversion IHe1 ; subst.
      apply Rel_step with (e1:=bind e0 (fun v => cast_erun v)) ; auto.
      apply MP.astep_bind_erun ; assumption.
      destruct (trans e3).
      constructor ; [auto | intros ; constructor].

      (* SubCase ERun, n>0 *)
      specialize (IHe1 e3 M1 M2 MemSvalue0 MemDepth0 BSLength H1).
      destruct (Context.shift (t :: t0)).
      destruct t1 ; simpl in *|-* ; auto.
      destruct p ; destruct (trans e3) ; intros.
      destruct IHe1 ; exists x.
      destruct H ; split ; [assumption|].
      destruct H0 ; [left | right] ; destruct H0.

        (* Case svalue *)
        destruct H2 ; destruct H3 ; subst.
        repeat(split ; auto).
        unfold admin_ssubst ; intros.
        rewrite MP.ssubst_bind with (f2:=fun v0 => cast_erun v0).
        constructor ; auto.
        intros ; constructor.
        apply functional_extensionality ; intros.
        rewrite MP.ssubst_erun ; auto.

        (* Case not svalue *)
        exists x0.
        destruct H0 ; destruct H2 ; subst ; auto.

      (* SubCase ERun, n=0, svalue 0 e *)
      simpl in *|-*.
      specialize (depth_length e2 (0::bs)) ; intros DpthLength2.
      specialize (length_svalue e2 (0::bs)) ; intros SValueLength.
      specialize (svalue_phi (CRaw.EBox e2) bs) ; intros SValuePhi.
      unfold trans_expr in SValuePhi ; simpl trans_expr in *|-*.
      simpl trans in *|-*.
      destruct (trans e2 (0::bs)).
      rewrite <- H in DpthLength ; destruct t ; simpl.
      clear IHe1 ; subst.
      apply Rel_step with (e1:=trans_expr e2 bs).
      assert(svalue 0 (CRaw.EBox e2)) as SValue0Box.
      constructor ; apply SValueLength ; auto.
      rewrite SValuePhi ; auto.
      apply MP.astep_bind_2 ; auto.
      simpl.
      unfold trans_expr ; simpl.
      rewrite trans_depth_0 with (bs2:=bs) ; auto.
      specialize (MP.astep_erun (trans_mem M2 bs) e2 bs) ; intros AStepERun.
      unfold trans_expr in AStepERun.
      destruct (trans e2 bs).
      apply AStepERun ; auto.
      constructor.
      apply SValueLength in H1.
      exfalso ; generalize H1 ; clear ; simpl ; intros ; omega.

    (* Case ELift *)
    admit.
  Qed.

  Theorem sstep_rstep_O:
    forall (e1 e2:S.expr) (M1 M2:S.Memory.t),
    let bs := 0::nil in
    depth e1 = 0 ->
    memory_svalue 0 M1 ->
    memory_depth M1 = 0 ->
    S.sstep 0 (M1, e1) (M2, e2) -> 
    rstep (trans_mem M1 bs, trans_expr e1 bs) 
      (trans_mem M2 bs, trans_expr e2 bs).
  Proof.
    intros.
    specialize (sstep_rstep e1 bs e2 M1 M2 H0) ; intros.
    simpl in H3.
    specialize (depth_length e1 bs) ; intros.
    unfold trans_expr ; destruct (trans e1).
    rewrite H in H4 ; destruct t ; [|inversion H4].
    rewrite H in *|-*.
    apply H3 ; auto.
  Qed.

End TranslationProperties.
