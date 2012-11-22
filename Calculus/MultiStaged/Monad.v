Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.MinMax.
Require Import Coq.Bool.Bool.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalChoice.
Require Import "Misc/Library".
Require Import "Misc/Injection".
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
    | (eh,h) :: c => (ssubst n ss (M.cast_var (hole_var x)) eh v, h) ::
        (ssubst_context n (if beq_nat x h
        then (StageSet.add n ss) else ss) x c v)
    end.

  Fixpoint ssubst_stack (n:nat) (ss:StageSet.t) 
    (x:M.S.var) (cs:t_stack) (v:expr) : t_stack :=
    match cs with
    | nil => nil
    | c :: cs => (ssubst_context n ss x c v) ::
       (ssubst_stack (pred n) ss x cs v)
    end.

End Context.

(* Translation R T <: StagedTranslation (Calculus R) T. *)
Module Translation (R:Replacement) 
    (T:StagedCalculus) (M:Monad R T). 

  Module S := M.S.
  Module Context := Context R T M.
  Import S.CRaw.

  Fixpoint trans (e:S.expr) (acc:Injection.t) : T.expr * Context.t_stack :=
    match e with
    | EConst i => (M.ret (M.cast_econst i), Context.empty)
    | EVar y => (M.ret (M.cast_evar (M.cast_var (source_var y))), Context.empty)
    | EAbs y e => 
        let (e,cs) := trans e acc in
        (M.ret (M.cast_eabs (M.cast_var (source_var y)) e), cs)
    | EFix f y e => 
        let (e,cs) := trans e acc in
        (M.ret (M.cast_efix 
            (M.cast_var (source_var f)) 
            (M.cast_var (source_var y)) e), cs)
    | EApp e1 e2 => 
        let (e1, cs1) := trans e1 (Injection.left acc) in
        let (e2, cs2) := trans e2 (Injection.right acc) in
        (M.bind e1
        (fun v1 => M.bind e2
        (fun v2 => M.cast_eapp v1 v2)), 
        Context.merge cs1 cs2)
    | ELoc l => (M.ret (M.cast_eloc l), Context.empty)
    | ERef e => 
        let (e,cs) := trans e acc in
        (M.bind e (fun v => M.cast_eref v), cs)
    | EDeref e => 
        let (e,cs) := trans e acc in
        (M.bind e (fun v => M.cast_ederef v), cs)
    | EAssign e1 e2 =>
        let (e1, cs1) := trans e1 (Injection.left acc) in
        let (e2, cs2) := trans e2 (Injection.right acc) in
        (M.bind e1
        (fun v1 => M.bind e2
        (fun v2 => M.cast_eassign v1 v2)), 
        Context.merge cs1 cs2)
    | EBox e => 
        let (e, cs) := trans e acc in
        match cs with
        | nil => (M.ret (M.cast_ebox e), Context.empty)
        | c :: cs => (Context.fill c (M.ret (M.cast_ebox e)), cs)
        end
    | EUnbox e =>
       let (e', cs) := trans e (Injection.right acc) in
       (M.cast_eunbox (M.cast_evar 
	(M.cast_var (hole_var (Injection.get acc 0)))), ((e', Injection.get acc 0) :: nil) :: cs)
    | ERun e =>
        let (e,cs) := trans e acc in
        (M.bind e (fun v => M.cast_erun v), cs)
    | ELift e =>
        let (e,cs) := trans e acc in
        (M.bind e (fun v => M.cast_elift v), cs)
    end.

  Definition trans_expr (e:S.expr) (acc:Injection.t) : T.expr :=
    let (e, _) := trans e acc in e.

  Fixpoint trans_mem (m:S.Memory.t) (acc:Injection.t) : T.Memory.t :=
    match m with
    | nil => nil
    | e :: m => trans_expr e acc :: (trans_mem m acc)
    end.

  Definition phi (e:S.expr) (acc:Injection.t) : T.expr :=
    match e with
    | EConst i => M.cast_econst i
    | EVar y => M.cast_evar (M.cast_var (source_var y))
    | EAbs y e => 
        let (e, _) := trans e acc in
        M.cast_eabs (M.cast_var (source_var y)) e
    | EFix f y e => 
        let (e, _) := trans e acc in
        M.cast_efix 
            (M.cast_var (source_var f)) 
            (M.cast_var (source_var y)) e
    | ELoc l => M.cast_eloc l
    | EBox e => 
        let (e, _) := trans e acc in
        M.cast_ebox e
    | _ => M.cast_econst 0
    end.

  (** ** Alpha Renaming Step *)
  Inductive alpha_rename (alpha:Injection.t) : relation T.expr :=
    | Alpha_const : forall (c:nat),
	alpha_rename alpha (M.cast_econst c) (M.cast_econst c)
    | Alpha_var_source : forall (x:S.var),
        alpha_rename alpha 
          (M.cast_evar (M.cast_var (source_var x)))
          (M.cast_evar (M.cast_var (source_var x)))
    | Alpha_var_hole : forall (x:S.var),
        alpha_rename alpha 
          (M.cast_evar (M.cast_var (hole_var x)))
          (M.cast_evar (M.cast_var (hole_var (Injection.get alpha x))))
    | Alpha_abs_source : forall (x:S.var) (e1 e2:T.expr),
        alpha_rename alpha e1 e2 -> 
          alpha_rename alpha 
          (M.cast_eabs (M.cast_var (source_var x)) e1) 
          (M.cast_eabs (M.cast_var (source_var x)) e2)
    | Alpha_abs_hole : forall (x:S.var) (e1 e2:T.expr),
        alpha_rename alpha e1 e2 -> 
          alpha_rename alpha 
          (M.cast_eabs (M.cast_var (hole_var x)) e1) 
          (M.cast_eabs (M.cast_var (hole_var (Injection.get alpha x))) e2)
    | Alpha_fix : forall (f x:S.var) (e1 e2:T.expr),
        alpha_rename alpha e1 e2 -> 
          alpha_rename alpha 
            (M.cast_efix (M.cast_var (source_var f)) (M.cast_var (source_var x)) e1)
            (M.cast_efix (M.cast_var (source_var f)) (M.cast_var (source_var x)) e2)
    | Alpha_app : forall (e1 e2 e3 e4:T.expr),
        alpha_rename alpha e1 e3 -> alpha_rename alpha e2 e4 -> 
        alpha_rename alpha (M.cast_eapp e1 e2) (M.cast_eapp e3 e4)
    | Alpha_loc : forall (l:nat),
	alpha_rename alpha (M.cast_eloc l) (M.cast_eloc l)
    | Alpha_ref : forall (e1 e2:T.expr),
        alpha_rename alpha e1 e2 -> 
        alpha_rename alpha (M.cast_eref e1) (M.cast_eref e2)
    | Alpha_deref : forall (e1 e2:T.expr),
        alpha_rename alpha e1 e2 -> 
          alpha_rename alpha (M.cast_ederef e1) (M.cast_ederef e2)
    | Alpha_assign : forall (e1 e2 e3 e4:T.expr),
        alpha_rename alpha e1 e3 -> alpha_rename alpha e2 e4 -> 
        alpha_rename alpha (M.cast_eassign e1 e2) (M.cast_eassign e3 e4)
    | Alpha_box : forall (e1 e2:T.expr),
        alpha_rename alpha e1 e2 -> 
          alpha_rename alpha (M.cast_ebox e1) (M.cast_ebox e2)
    | Alpha_unbox : forall (e1 e2:T.expr),
        alpha_rename alpha e1 e2 ->
          alpha_rename alpha (M.cast_eunbox e1) (M.cast_eunbox e2)
    | Alpha_run : forall (e1 e2:T.expr),
        alpha_rename alpha e1 e2 -> 
          alpha_rename alpha (M.cast_erun e1) (M.cast_erun e2)
    | Alpha_lift : forall (e1 e2:T.expr),
        alpha_rename alpha e1 e2 -> 
          alpha_rename alpha (M.cast_elift e1) (M.cast_elift e2)
    | Alpha_ret : forall (e1 e2:T.expr),
        alpha_rename alpha e1 e2 -> 
          alpha_rename alpha (M.ret e1) (M.ret e2)
    | Alpha_bind : forall (e1 e2 e3 e4:T.expr) (f1 f2:T.expr -> T.expr),
        alpha_rename alpha e1 e2 -> 
        alpha_rename alpha
          (f1 (M.cast_evar (M.cast_var (source_var 0))))
          (f2 (M.cast_evar (M.cast_var (source_var 0)))) ->
        alpha_rename alpha (M.bind e1 f1) (M.bind e2 f2).

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
    | Admin_reduc : forall (e:expr) (acc:Injection.t), svalue 1 e ->
        admin (M.cast_eunbox (M.cast_ebox (trans_expr e acc))) 
          (trans_expr e acc).

  Definition admin_context :  relation Context.t := 
    Context.congr_context admin.
  Definition admin_stack : relation Context.t_stack := 
    Context.congr_stack admin.

  Inductive alpha_rename_context (alpha: Injection.t) : relation Context.t :=
    | AlphaCtx_nil: alpha_rename_context alpha nil nil
    | AlphaCtx_cons: forall (k1 k2:Context.t) (e1 e2:T.expr) (x:M.S.var),
        alpha_rename_context alpha k1 k2 -> 
        alpha_rename alpha e1 e2 -> 
        alpha_rename_context alpha ((e1,x)::k1) ((e2,(Injection.get alpha x))::k2).

  Inductive alpha_rename_stack (alpha:Injection.t) : relation Context.t_stack :=
    | AlphaStack_empty: alpha_rename_stack alpha nil nil
    | AlphaStack_context: forall (s1 s2:Context.t_stack) (k1 k2:Context.t),
       alpha_rename_stack alpha s1 s2 -> alpha_rename_context alpha k1 k2 ->
       alpha_rename_stack alpha (k1::s1) (k2::s2).

  (** ** Relative Abstract Reduction Step *)
  Inductive rstep : relation T.state :=
    | Rel_step : forall (s:T.state) (e1 e2 e3:T.expr) (M:T.Memory.t),
        M.astep s (M,e1) -> admin e1 e2 -> 
        (exists f, alpha_rename f e2 e3) -> rstep s (M,e3).

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

  Parameter ssubst_eref :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_eref e) v
       = cast_eref (ssubst n ss (cast_var x) e v).

  Parameter ssubst_deref :
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

  (** Abstract Reduction Properties *)

  Parameter astep_bind_1 :
    forall (e1 e2 ef:expr) (acc:Injection.t) (M1 M2:Memory.t) (x:var),
    let f := fun v => cast_eapp (cast_eabs x ef) v in
    astep (M1, e1) (M2, e2) ->
    astep (M1, bind e1 f) (M2, bind e2 f).

  Parameter astep_bind_2 :
    forall (v:S.expr) (e:expr) (acc:Injection.t) (M1 M2:Memory.t) (f:expr -> expr),
    S.svalue 0 v -> astep (M1, (f (phi v acc))) (M2, e) ->
    astep (M1, (bind (ret (phi v acc)) f)) (M2, e).

  Parameter astep_app_abs :
    forall (v:S.expr) (x:S.var) (e:expr) (acc:Injection.t) (M:Memory.t),
    S.svalue 0 v -> astep (M, cast_eapp
      (cast_eabs (cast_var x) e) (phi v acc))
      (M, ssubst 0 StageSet.empty (cast_var x) e (phi v acc)).

End MonadProperties.

Module ContextStaticProperties (R:Replacement)
  (T:StagedCalculus) (M:Monad R T).

  Module Context := Context R T M.
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

End ContextStaticProperties.

Module ContextProperties (R:Replacement) (T:StagedCalculus) 
    (M:Monad R T) (MP:MonadProperties R T M).

  Module Context := Context R T M.
  Module StaticProperties := ContextStaticProperties R T M.
  Import StaticProperties.
  Import MP.Translation.
  Import M.
  Import Context.

  Lemma fill_ssubst:
    forall (acc:Injection.t) (c:t) (n:nat) (ss:StageSet.t) (x:S.var) (v:S.expr) (e:T.expr),
    S.svalue 0 v -> VarSet.mem x (context_hole_set c) = false ->
      fill (ssubst_context n ss x c (phi v acc)) 
      (ssubst n ss (M.cast_var (hole_var x)) e (phi v acc)) = 
      ssubst n ss (cast_var (hole_var x)) (fill c e) (phi v acc).
    intros.
    induction c ; simpl.
    reflexivity.

    destruct a ; simpl in *|-*.
    assert(H1 := H0).
    apply VarSetProperties.add_mem_6 in H0.
    apply beq_nat_false_iff in H0.
    rewrite beq_nat_sym in H0.
    rewrite H0.
    rewrite IHc.
    rewrite MP.ssubst_bind with (f2 :=(fun v1 : T.expr =>
     cast_eapp
     (cast_eabs (cast_var (hole_var v0))
        (ssubst n ss (cast_var (hole_var x)) (fill c e) (phi v acc))) v1)).
    reflexivity.

    apply functional_extensionality.
    intros.
    rewrite MP.ssubst_eapp.
    rewrite MP.ssubst_eabs.
    assert(S.beq_var (hole_var x) (hole_var v0) = false).
    apply beq_nat_false_iff.
    apply beq_nat_false_iff in H0.
    unfold not ; intros ; apply H0.
    unfold hole_var in H2.
    omega.
    rewrite H2.
    reflexivity.
    apply VarSetProperties.add_mem_5 in H1.
    assumption.
  Qed.


End ContextProperties.

Module TranslationStaticProperties (R:Replacement) 
    (T:StagedCalculus) (M:Monad R T).

  Module Translation := Translation R T M.
  Module CalculusProperties := CalculusProperties R M.S.
  Module ContextStaticProperties := ContextStaticProperties R T M.
  Import Translation.
  Import M.S.
  Import M.

  Lemma depth_length:
    forall (e:expr) (acc:Injection.t),
    let (_, cs) := trans e acc in
    depth e = length cs.
  Proof.
    induction e ; simpl ; intros ;
    try(auto ; fail) ;
    try(specialize (IHe acc) ; destruct (trans e acc) ; auto ; fail) ;
    try(specialize (IHe1 (Injection.left acc)) ;
    specialize (IHe2 (Injection.right acc)) ;
    destruct (trans e1) ; 
    destruct (trans e2) ;
    simpl ; rewrite ContextStaticProperties.merge_length ; auto ; fail).
    

    destruct (depth e).
    specialize (IHe acc).
    destruct (trans e).
    destruct t ; simpl in *|-*.
    reflexivity.
    inversion IHe.

    specialize (IHe acc).
    destruct (trans e).
    destruct t ; simpl in *|-*.
    inversion IHe.
    inversion IHe.
    reflexivity.

    specialize (IHe (Injection.right acc)).
    destruct (trans e).
    simpl.
    auto.
  Qed.

  Lemma length_svalue:
    forall (e:expr) (acc:Injection.t) (n:nat),
    let (_, cs) := trans e acc in
    length cs < (S n) <-> svalue (S n) e.
  Proof.
    intros.
    specialize (depth_length e) ; intros.
    specialize (H acc).
    destruct (trans e).
    rewrite <- H.
    apply CalculusProperties.depth_svalue.
  Qed.

  Lemma svalue_phi:
    forall (e:expr) (acc:Injection.t),
    svalue 0 e -> trans_expr e acc = M.ret (phi e acc).
  Proof.
    intros ; inversion H ; subst ; simpl ;
    try(reflexivity) ;
    try(unfold trans_expr ; simpl ; 
    destruct (trans e0) ; reflexivity).

    unfold trans_expr.
    simpl.
    inversion H ; subst.
    specialize (length_svalue e0 acc 0) ; intros.
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
    forall (e:expr) (acc:Injection.t),
    let (_, cs) := trans e acc in
    ~ In nil cs.
  Proof.
    induction e ; intros ; simpl ; auto ;

    try( specialize (IHe acc) ; destruct (trans e) ; auto ; fail) ;

    try(specialize (IHe1 (Injection.left acc)) ;
    specialize (IHe2 (Injection.right acc)) ;
    destruct (trans e1) ; destruct (trans e2) ;
    unfold not ; intros ;
    apply context_merge_not_nil in H ;
    tauto ; fail).


    specialize (IHe acc).
    destruct (trans e).
    destruct t ; simpl.
    tauto.
    unfold not ; intros ; apply IHe.
    simpl ; auto.
    
    specialize (IHe (Injection.right acc)).
    destruct (trans e).
    unfold not ; intros ; apply IHe.
    simpl in *|-*.
    destruct H.
    inversion H.
    assumption.
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

  Lemma admin_context_context:
    forall (k1 k2 k3 k4:Context.t),
    admin_context k1 k2 -> admin_context k3 k4 ->
    admin_context (k1 ++ k3) (k2 ++ k4).
  Proof.
    unfold admin_context ;
    induction k1 ; intros.
    inversion H ; subst.
    simpl ; assumption.

    destruct a ; inversion H ; subst.
    simpl ; apply Context.CongrCtx_cons.
    apply IHk1 ; assumption.
    assumption.
  Qed.

  Lemma admin_context_merge:
    forall (cs1 cs2 cs3 cs4:Context.t_stack),
    admin_stack cs1 cs2 ->
    admin_stack cs3 cs4 ->
    admin_stack (Context.merge cs1 cs3) (Context.merge cs2 cs4).
  Proof.
     induction cs1 ; intros ;
     inversion H ; subst ; simpl.

     assumption.

     destruct cs3 ;
     inversion H0 ; subst.
     assumption.
     apply Context.CongrStack_context.
     apply IHcs1 ; assumption.
     apply admin_context_context ;
     [inversion H | inversion H0] ; subst ;
     assumption.
  Qed.


  Lemma alpha_rename_stack_app_refl:
    forall (cs1 cs2:Context.t_stack),
    alpha_rename_stack Injection.id cs1 cs1 ->
    alpha_rename_stack Injection.id cs2 cs2 ->
    alpha_rename_stack Injection.id (cs1 ++ cs2) (cs1 ++ cs2).
  Proof.
    induction cs1 ; simpl ; intros.
    assumption.
    inversion H ; inversion H0 ; subst.
    rewrite app_nil_r.
    assumption.
    constructor.
    apply IHcs1.
    assumption.
    assumption.
    assumption.
  Qed.

  Lemma alpha_rename_context_app:
    forall (c1 c2 c3 c4:Context.t) (alpha:Injection.t),
    alpha_rename_context alpha c1 c3 ->
    alpha_rename_context alpha c2 c4 ->
    alpha_rename_context alpha (c1++c2) (c3++c4).
  Proof.
    induction c1 ; simpl ; intros.
    inversion H ; subst.
    assumption.
    inversion H ; subst.
    constructor.
    apply IHc1 ; assumption.
    assumption.
  Qed.

  Lemma alpha_rename_merge:
    forall (cs1 cs2 cs3 cs4:Context.t_stack) (alpha:Injection.t),
    alpha_rename_stack alpha cs1 cs3 ->
    alpha_rename_stack alpha cs2 cs4 ->
    alpha_rename_stack alpha (Context.merge cs1 cs2) (Context.merge cs3 cs4).
  Proof.
    induction cs1 ; simpl ; intros.
    inversion H ; subst.
    assumption.
    inversion H ; subst.
    destruct cs2.
    inversion H0 ; subst.
    simpl.
    assumption.
    simpl.
    inversion H0 ; subst.
    constructor.
    apply IHcs1.
    assumption.
    assumption.
    apply alpha_rename_context_app.
    assumption.
    assumption.
  Qed.

  Lemma alpha_rename_fill:
    forall (e1 e2:T.expr) (c1 c2:Context.t) (alpha:Injection.t),
    alpha_rename alpha e1 e2 ->
    alpha_rename_context alpha c1 c2 ->
    alpha_rename alpha (Context.fill c1 e1) (Context.fill c2 e2).
  Proof.
    induction c1 ; intros.
    inversion H0 ; simpl ; subst.
    assumption.
    destruct a.
    inversion H0 ; subst.
    simpl.
    constructor ; auto.
    constructor.
    constructor.
    apply IHc1 ; assumption.
    constructor.
  Qed.

  Lemma injective_composition:
    forall (alpha1 alpha2:Injection.t),
    let f := fun v => (Injection.get alpha2 (Injection.get alpha1 v)) in
    forall (m n:nat), m <> n -> f m <> f n.
  Proof.
    intros.
    unfold f.
    apply (Injection.injective alpha2).
    apply (Injection.injective alpha1).
    assumption.
  Qed.

  Lemma alpha_rename_acc:
    forall (e:S.expr) (acc1 acc2 alpha:Injection.t),
    let (e1, cs1) := trans e acc1 in
    let (e2, cs2) := trans e acc2 in
    (forall n:nat, Injection.get alpha (Injection.get acc1 n) = 
      Injection.get acc2 n) ->
    alpha_rename alpha e1 e2 /\
    alpha_rename_stack alpha cs1 cs2.
  Proof.
    induction e ; simpl in *|-* ; intros ;
    
    try(split ; repeat(constructor) ; auto ; fail) ;

    try(specialize (IHe acc1 acc2 alpha) ;
    destruct (trans e) ; destruct (trans e) ; intros ;
    specialize (IHe H) ; destruct IHe ;
    split ; repeat(constructor) ; auto ; fail).

    specialize (IHe1 (Injection.left acc1) (Injection.left acc2) alpha) ;
    specialize (IHe2 (Injection.right acc1) (Injection.right acc2) alpha) ;
    destruct (trans e1) ; destruct (trans e1) ;
    destruct (trans e2) ; destruct (trans e2) ; intros ;
    unfold Injection.left in IHe1 ; unfold Injection.right in IHe2.
    assert(alpha_rename alpha e e0 /\ alpha_rename_stack alpha t t0).
    apply IHe1 ; intros ; apply H.
    assert(alpha_rename alpha e3 e4 /\ alpha_rename_stack alpha t1 t2).
    apply IHe2 ; intros ; apply H.
    destruct H0 ; destruct H1 ;
    split ; [apply Alpha_bind ; auto ;
    repeat(constructor) ; auto | 
    apply alpha_rename_merge ; auto ].

    
    (* Should be merged with previous case *)
    specialize (IHe1 (Injection.left acc1) (Injection.left acc2) alpha) ;
    specialize (IHe2 (Injection.right acc1) (Injection.right acc2) alpha) ;
    destruct (trans e1) ; destruct (trans e1) ;
    destruct (trans e2) ; destruct (trans e2) ; intros ;
    unfold Injection.left in IHe1 ; unfold Injection.right in IHe2.
    assert(alpha_rename alpha e e0 /\ alpha_rename_stack alpha t t0).
    apply IHe1 ; intros ; apply H.
    assert(alpha_rename alpha e3 e4 /\ alpha_rename_stack alpha t1 t2).
    apply IHe2 ; intros ; apply H.
    destruct H0 ; destruct H1 ;
    split ; [apply Alpha_bind ; auto ;
    repeat(constructor) ; auto | 
    apply alpha_rename_merge ; auto ].
    
    specialize (IHe acc1 acc2 alpha).
    destruct (trans e) ; destruct (trans e).
    destruct t ; simpl.
    destruct t0 ; simpl ; intros ;
    specialize (IHe H) ; destruct IHe.
    split ; repeat(constructor) ; auto.
    inversion H1.
    destruct t0 ; simpl ; intros ;
    specialize (IHe H) ; destruct IHe ;
    inversion H1 ; subst.
    split ; repeat(constructor) ; auto.
    apply alpha_rename_fill ; auto.
    repeat(constructor) ; auto.

    specialize (IHe (Injection.right acc1) (Injection.right acc2) alpha).
    destruct (trans e) ; destruct (trans e).
    intros.
    unfold Injection.right in IHe.
    assert(alpha_rename alpha e0 e1 /\ alpha_rename_stack alpha t t0).
    apply IHe ; intros ; apply H.
    destruct H0.
    split.
    repeat(constructor) ; auto.
    rewrite <- H ; constructor.
    rewrite <- H ; constructor ; auto.
    repeat(constructor) ; auto.
  Qed.

  Definition R (acc1 acc2:Injection.t) (x y:nat) : Prop := 
    (exists z, x = (Injection.get acc1 z) /\ y = (Injection.get acc2 z)).

  Lemma R_injective_relation:
    forall (acc1 acc2:Injection.t),
    Injection.injective_relation (R acc1 acc2).
  Proof.
    unfold Injection.injective_relation ; intros.
    unfold R in *|-*.
    destruct H ; destruct H0.
    destruct H ; destruct H0.
    specialize (Injection.injective acc2 x x0) ; intros.
    assert(x = x0).
    omega.
    subst ; reflexivity.
  Qed.

  Lemma R_partial_function:
    forall (acc1 acc2:Injection.t),
    partial_function (R acc1 acc2).
  Proof.
    unfold partial_function ; intros.
    unfold R in *|-*.
    destruct H ; destruct H0.
    destruct H ; destruct H0.
    subst.
    specialize (Injection.injective acc1 x0 x1) ; intros.
    assert(x0 = x1).
    omega.
    subst ; reflexivity.
  Qed.
   
  Lemma alpha_rename_left_acc_exists:
    forall (e:S.expr) (acc1 acc2:Injection.t),
    let acc2 := Injection.left acc2 in
    let (e1, cs1) := trans e acc1 in
    let (e2, cs2) := trans e acc2 in
    exists alpha:Injection.t,
    alpha_rename alpha e1 e2 /\
    alpha_rename_stack alpha cs1 cs2.
  Proof.
    intros.
    specialize (R_injective_relation acc1 acc0) ; intros.
    specialize (R_partial_function acc1 acc0) ; intros.
    assert(Injection.disjoint_function (R acc1 acc0)
       (Injection.right acc2)).
       unfold Injection.disjoint_function ; intros.
       unfold Injection.not_in_image, Injection.left, Injection.right.
       unfold R ; simpl ; intros.
       apply all_not_not_ex ; intros.
       apply or_not_and ; right.
       apply (Injection.injective acc2).
       omega.
    specialize (Injection.completion_exists 
     (R acc1 (Injection.left acc2)) (Injection.right acc2) H H0 H1) ; intros.
    destruct H2 ; unfold R in H2.
    specialize (alpha_rename_acc e acc1 acc0 x) ; intros.
    destruct (trans e).
    destruct (trans e).
    exists x.
    apply H3 ; intros.
    specialize (H2 (Injection.get acc1 n) (Injection.get acc0 n)).
    apply H2.
    exists n.
    split ; auto.
  Qed.

  Lemma alpha_rename_right_acc_exists:
    forall (e:S.expr) (acc1 acc2:Injection.t),
    let acc2 := Injection.right acc2 in
    let (e1, cs1) := trans e acc1 in
    let (e2, cs2) := trans e acc2 in
    exists alpha:Injection.t,
    alpha_rename alpha e1 e2 /\
    alpha_rename_stack alpha cs1 cs2.
  Proof.
    intros.
    specialize (R_injective_relation acc1 acc0) ; intros.
    specialize (R_partial_function acc1 acc0) ; intros.
    assert(Injection.disjoint_function (R acc1 acc0)
       (Injection.left acc2)).
       unfold Injection.disjoint_function ; intros.
       unfold Injection.not_in_image, Injection.right, Injection.left.
       unfold R ; simpl ; intros.
       apply all_not_not_ex ; intros.
       apply or_not_and ; right.
       apply (Injection.injective acc2).
       omega.
    specialize (Injection.completion_exists 
     (R acc1 (Injection.right acc2)) (Injection.left acc2) H H0 H1) ; intros.
    destruct H2 ; unfold R in H2.
    specialize (alpha_rename_acc e acc1 acc0 x) ; intros.
    destruct (trans e).
    destruct (trans e).
    exists x.
    apply H3 ; intros.
    specialize (H2 (Injection.get acc1 n) (Injection.get acc0 n)).
    apply H2.
    exists n.
    split ; auto.
  Qed.

  Lemma alpha_rename_refl:
    forall (e:S.expr) (acc:Injection.t),
    let (e, cs) := trans e acc in
    alpha_rename Injection.id e e /\
    alpha_rename_stack Injection.id cs cs.
  Proof.
    intros.
    specialize (alpha_rename_acc e acc acc Injection.id) ; intros.
    destruct (trans e).
    apply H ; intros.
    reflexivity.
  Qed.

End TranslationStaticProperties.

Module TranslationProperties (R:Replacement) 
    (T:StagedCalculus) (M:Monad R T) (MP:MonadProperties R T M). 

  Module StaticProperties := TranslationStaticProperties R T M.
  Module Translation := MP.Translation.
  Module ContextProperties := ContextProperties R T M MP.
  Module CalculusProperties := CalculusProperties R M.S.
  Import StaticProperties.
  Import Translation.
  Import M.S.
  Import M.

  Lemma context_stack_independent:
    forall (e:expr) (acc:Injection.t),
      let (_, cs) := trans e acc in
      match Context.shift cs with
        | ((_, h) :: c, cs) => 
          VarSet.mem h (Context.context_hole_set c) = false /\ 
          VarSet.mem h (Context.stack_hole_set cs) = false
        | _ => True
      end.
  Proof.
    induction e ; simpl ; intros ; auto ;
    try(specialize (IHe acc) ; destruct (trans e) ; assumption ; fail) ;
    admit.
    (* TODO: Prove it *)
  Qed.

  Lemma context_expr_subst:
    forall (h:var) (e v:T.expr) (c:Context.t) (n:nat),
      VarSet.mem h (Context.context_hole_set c) = false ->
      ssubst n StageSet.empty (M.cast_var (hole_var h)) (Context.fill c e) v =
      Context.fill (Context.ssubst_context n StageSet.empty h c v) 
      (ssubst n StageSet.empty (M.cast_var (hole_var h)) e v).
  Proof.
    induction c ; intros ; simpl.
    reflexivity.
    destruct a.
    specialize (IHc n).
    simpl in H.
    assert(H0 := H).
    apply VarSetProperties.add_mem_5 in H0.
    apply IHc in H0.
    clear IHc.
    assert(beq_nat h v0 = false).
    apply VarSetProperties.add_mem_6 in H.
    apply beq_nat_false_iff ; auto.
    rewrite H1.
    simpl.
    rewrite <- H0.
    apply MP.ssubst_bind.
    apply functional_extensionality.
    intros.
    rewrite MP.ssubst_eapp.
    rewrite MP.ssubst_eabs.
    assert(beq_var (hole_var h) (hole_var v0) = false).
    unfold hole_var.
    apply beq_nat_false_iff ;
    apply beq_nat_false_iff in H1.
    omega.
    rewrite H2 ; reflexivity.
  Qed.

  Lemma test:
    forall (e1:S.expr) (acc:Injection.t) (e2:S.expr) (M1 M2:S.Memory.t),
    rstep (trans_mem M1 acc, trans_expr e1 acc) (trans_mem M2 acc, trans_expr e2 acc) ->
    forall (acc:Injection.t),
    rstep (trans_mem M1 acc, trans_expr e1 acc) (trans_mem M2 acc, trans_expr e2 acc).
  Proof.
    admit. (* Prove it *)
  Qed.

  (* En gros, on distingue 2 mondes de variables:
    - les variables traduites (cast_var) qui sont celles 
   des expressions initiales et celles créées pour le contexte
    - les variables des opérateurs monadiques.
   On peut implémenter ça par une séparation par parité: cast_var
   enverrait n vers 2n, etles variables des opérateurs monadiques
   seraient 2n+1.
  *)
  Lemma sstep_rstep:
    forall (e1:S.expr) (acc:Injection.t) (e2:S.expr) (M1 M2:S.Memory.t),
    let (e1', cs1) := trans e1 acc in
    let n := length cs1 in
    S.sstep n (M1, e1) (M2, e2) -> 
    match cs1 with
    | nil => rstep (trans_mem M1 acc, e1') (trans_mem M2 acc, trans_expr e2 acc)
    | cs1 => let (c1, cs1') := Context.shift cs1 in
      match c1 with
      | nil => False
      | cons (t_eh, h) c1' => 
          let (e2', cs2) := trans e2 acc in
          let M1' := trans_mem M1 acc in
          let M2' := trans_mem M2 acc in
          exists eh, t_eh = trans_expr eh acc /\
          (
            S.svalue 0 eh /\ 
            M1 = M2 /\ 
            admin_stack 
              (Context.ssubst_stack 
                 (pred n) StageSet.empty h (Context.unshift cs1' c1') (phi eh acc)) cs2 /\
            admin
               (M.ssubst n StageSet.empty (M.cast_var (hole_var h)) e1' (phi eh acc)) e2'
          \/ 
            exists eh', let t_eh' := trans_expr eh' acc in
            rstep (M1', t_eh) (M2', t_eh') /\
            e1' = e2' /\
            cs2 = Context.unshift cs1' ((t_eh', h) :: c1')
          )
      end
    end.
  Proof.
    induction e1 ; simpl ; intros.

    (* Case EConst *)
    inversion H.

    (* Case EVar *)
    inversion H.

    (* Case EAbs *)
    specialize (IHe1 acc).
    destruct (trans e1).
    intros.

    destruct t ; simpl in H;
    inversion H ; subst.
    specialize (IHe1 e3 M1 M2 H2).
    destruct (Context.shift (t :: t0)).
    destruct t1 ; simpl in *|-*.
      destruct (trans e3).
      destruct IHe1 ; subst ; tauto.

      assumption.

      destruct p ; destruct (trans e3).
      destruct IHe1.
      exists x.
      destruct H0.
      split ; [assumption|].
      destruct H1 ; [left | right] ;
      destruct H1.
        destruct H3.
        destruct H4.
        subst.
        repeat(split ; auto).

      rewrite MP.ssubst_ret, MP.ssubst_eabs.
      apply Admin_ret, Admin_abs.

      assert(S.beq_var (hole_var v0) (source_var v) = false).
        apply beq_nat_false_iff.
        unfold hole_var, source_var.
        omega.

      simpl in H0.
      rewrite H0 ; assumption.
      exists x0.
      destruct H1 ; destruct H3 ; subst.
      auto.

    (* Case EFix *)
    specialize (IHe1 acc).
    destruct (trans e1).
    intros.

    destruct t ; simpl in H;
    inversion H ; subst.
    specialize (IHe1 e3 M1 M2 H2).
    destruct (Context.shift (t :: t0)).
    destruct t1 ; simpl in *|-*.
      destruct (trans e3).
      destruct IHe1 ; subst ; tauto.
      assumption.

      destruct p ; destruct (trans e3).
      destruct IHe1.
      exists x.
      destruct H0 ; split ; [assumption|].
      destruct H1 ; [left | right] ; destruct H1.
      destruct H3 ; destruct H4.
      subst.
      repeat(split ; auto).

      rewrite MP.ssubst_ret, MP.ssubst_efix.
      apply Admin_ret, Admin_fix.

      assert(orb (S.beq_var (hole_var v1) (source_var v)) 
          (S.beq_var (hole_var v1) (source_var v0)) = false).
        apply orb_false_intro ; apply beq_nat_false_iff ;
        unfold hole_var, source_var ; omega.

      simpl in H0.
      rewrite H0 ; assumption.
      exists x0.
      destruct H1 ; destruct H3 ; subst ; auto.

    (* Case EApp *)
    admit.

    (* Case ELoc *)
    inversion H.

    (* Case ERef *)
    specialize (IHe1 acc).
    destruct (trans e1).
    intros.
    destruct t ; simpl in H ;
    inversion H ; subst.

      (* SubCase ERef, n=0, e -> e' *)
      specialize (IHe1 e3 M1 M2 H2).
      unfold trans_expr.
      unfold trans_expr in IHe1.
      simpl.
      destruct (trans e3).
      simpl.
      admit.

    
      (* SubCase ERef, n=0, svalue 0 e *)
      admit.

      (* SubCase ERef, n>0 *)
      specialize (IHe1 e3 M1 M2 H2).
      destruct (Context.shift (t :: t0)).
      destruct t1 ; simpl in *|-*.
        destruct (trans e3).
        destruct IHe1 ; subst ; tauto.
        assumption.

        destruct p ; destruct (trans e3).
        destruct IHe1.
        exists x.
        destruct H0 ; split ; [assumption|].
        destruct H1 ; [left | right] ; destruct H1.
        destruct H3 ; destruct H4.
        repeat(split ; auto).

        rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr => cast_eref v0)).
        apply Admin_bind.
        assumption.
        intros.
        apply Admin_refl.

        assert (
         (fun v2 => M.ssubst (S (length t0)) StageSet.empty (M.cast_var (hole_var v)) (M.cast_eref v2) (phi x acc)) =
         (fun v2 => M.cast_eref (M.ssubst (S (length t0)) StageSet.empty (M.cast_var (hole_var v)) v2 (phi x acc)))).
          apply functional_extensionality.
          intros ; apply MP.ssubst_eref.
        assumption.
        exists x0.
        destruct H1 ; destruct H3 ; subst ; auto.

    (* Case EDeref *)
    admit.

    (* Case EAssign *)
    admit.

    (* Case EBox *)
    
    specialize (length_svalue e1 acc 0) ; intros.
    specialize (context_stack_not_nil e1 acc) ; intros.
    specialize (context_stack_independent e1 acc) ; intros.
    specialize (IHe1 acc).
    destruct (trans e1).
    destruct t ; simpl in *|-* ; intros.

      (* Case of empty stack. Impossible *)
      inversion H2 ; subst ; simpl in *|-*.
      destruct H.
      assert(svalue 1 e1).
      apply H ; omega.
      specialize (CalculusProperties.svalue_not_sprogresses 1 M1 e1 H4 (M2,e3) H5) ; intros.
      contradiction.

      (* Case of stack > 0 *)
      destruct t0.
      
        simpl in *|-*.

        (* Case of length(stack) = 1 *)
        inversion H2 ; subst ; simpl in *|-*.
        specialize (IHe1 e3 M1 M2 H5).
        destruct t.

          (* Case stack = [[]] Impossible *)
          exfalso ; assumption.
   
          (* Case stack = [a :: lst] *)
          destruct p ; clear H0.
          unfold trans_expr ; simpl.
          destruct (trans e3).
          destruct IHe1.
          destruct H0.
          destruct H3.

            (* Case svalue *)
            destruct H3 ; destruct H4 ; 
            destruct H6.
            subst.
            clear H.
            inversion H6 ; subst.
            inversion H4 ; subst ; clear H6 H4.
            simpl.
            apply Rel_step with (e1:=Context.fill 
               (Context.ssubst_context 0 StageSet.empty v t (phi x acc))
               (M.ssubst 0 StageSet.empty (M.cast_var (hole_var v)) 
               (M.ret (M.cast_ebox e)) (phi x acc)))
               (e2:=Context.fill k2 (ret (cast_ebox e2))).
            assert(H10 := H3).
            apply svalue_phi with (acc:=acc) in H10.
            rewrite H10.
            apply MP.astep_bind_2.
            assumption.
            rewrite ContextProperties.fill_ssubst.
            apply MP.astep_app_abs.
            assumption.
            assumption.
            destruct H1 ; assumption.
            apply admin_context_expr.
            assumption.
            rewrite MP.ssubst_ret.
            rewrite MP.ssubst_ebox.
            constructor.
            constructor.
            assumption.
            fail.

            (* Case not svalue *)
            destruct H3 ; destruct H3 ; destruct H4.
            inversion H3 ; subst.
            simpl.
            apply Rel_step with (e1:=bind e4 (fun v0 =>
               cast_eapp
               (cast_eabs (cast_var (hole_var v))
               (Context.fill t (ret (cast_ebox e2)))) v0)).
            apply MP.astep_bind_1 ; assumption.
            constructor ;
            [assumption | intros ; constructor].

        (* Case of length(stack) > 1 *)
        inversion H2 ; subst.
        specialize (IHe1 e3 M1 M2 H5).
        destruct (Context.shift (t0 :: t1)).
        destruct t2.
        assumption.
        destruct p.
        simpl.

        destruct (trans e3).
        
        destruct IHe1.
        destruct t4.
        destruct H3.
        destruct H4.
        destruct H4.
        destruct H6.
        destruct H7.
        inversion H7 ; subst.
        destruct H4.
        destruct H4.
        destruct H6.
        inversion H7.

        exists x.
        destruct H3.
        split ; [assumption |].
        destruct H4.

          (* Case svalue *)
          destruct H4.
          destruct H6.
          destruct H7.
          subst.
          left.
          repeat(split ; auto).

          inversion H7 ; subst.
          simpl in *|-*.*.
          assumption.
        
          simpl in *|-*.
          inversion H7 ; subst.
          rewrite context_expr_subst.
          apply admin_context_expr.
          assumption.
          
          rewrite MP.ssubst_ret.
          rewrite MP.ssubst_ebox.
          constructor.
          constructor.
          assumption.

          destruct H1.
          rewrite VarSetProperties.union_mem in H3.
          apply orb_false_iff in H3.
          destruct H3 ; assumption.

          (* Case not svalue *)
          destruct H4.
          destruct H4.
          destruct H6.
          inversion H7 ; subst.
          clear H7.
          right.
          exists x0.
          repeat(split ; auto).

    (* Case EUnbox *)
    specialize (IHe1 (Injection.succ acc)).
    specialize (test e1 (Injection.succ acc)) ; intros.
    unfold trans_expr in *|-*.
    destruct (trans e1).
    simpl in *|-* ; intros.
    inversion H0 ; subst.

      (* Case EUnbox -> EUnbox *)
      specialize (IHe1 e3 M1 M2 H3).
      specialize (H e3 M1 M2).
      destruct t.
      unfold trans_expr in *|-*.
      simpl in *|-*.
      assert(trans e3 (Injection.succ acc)  = 
        (trans ((fun x => x) e3) (Injection.succ acc) )).
      reflexivity.
      destruct (trans e3).
      exists e1.
      right.
      exists e3.
      repeat (split ; auto).
      specialize (H IHe1 acc).
      
      fail. (* TO prove *)
      destruct (trans e3).
      destruct (trans e3).
      admit.
      admit.

      (* Case EUnbox Box e -> e *)
      admit.

    (* Case ERun *)
    admit.

    (* Case ELift *)
    admit.
  Qed.

  Theorem sstep_rstep_O:
    forall (e1 e2:S.expr) (M1 M2:S.Memory.t),
    let acc := Injection.id in
    depth e1 = 0 ->
    S.sstep 0 (M1, e1) (M2, e2) -> 
    rstep (trans_mem M1 acc, trans_expr e1 acc) 
      (trans_mem M2 acc, trans_expr e2 acc).
  Proof.
    intros.
    specialize (sstep_rstep e1 acc e2 M1 M2) ; intros.

    assert(forall (e1':T.expr) (cs1:Context.t_stack), 
    trans e1 acc = (e1', cs1) -> cs1 = nil).
    intros.
      assert(0 = length cs1).
      rewrite <- H.
      specialize (depth_length e1) ; intros.
      specialize (H3 acc) ;
      rewrite H2 in H3 ; destruct H3.
      reflexivity.
    destruct cs1 ; simpl in *|-* ;
    [reflexivity | inversion H3].

    unfold trans_expr in *|-*.
    destruct (trans e1).
    specialize (H2 e t).
    rewrite H2 in H1.
    simpl in H1.
    destruct (trans e2).
    auto.
    auto.
  Qed.

End TranslationProperties.
