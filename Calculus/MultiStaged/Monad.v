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

  Definition hd_cons {T:Type} (l:list T) (e:T) : T * list T :=
    match l with
    | nil => (e, nil)
    | e :: l => (e, l)
    end.

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
        let (b, bs) := hd_cons bs 0 in
	let b2 := booker e2 0 in
        let (e1, cs1) := trans e1 ((b + b2)%nat::bs) in
        let (e2, cs2) := trans e2 (b::bs) in
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
	let (b, bs) := hd_cons bs 0 in
	let b2 := booker e2 0 in
        let (e1, cs1) := trans e1 ((b + b2)%nat::bs) in
        let (e2, cs2) := trans e2 (b::bs) in
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
        let (b, bs) := hd_cons bs 0 in
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

  Fixpoint trans_mem (m:S.Memory.t) (bs:list nat) : T.Memory.t :=
    match m with
    | nil => nil
    | e :: m => trans_expr e bs :: (trans_mem m bs)
    end.

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
       = cast_eunbox (ssubst (pred n) ss (cast_var x) e v).

  Parameter ssubst_erun :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_erun e) v
       = cast_erun (ssubst n ss (cast_var x) e v).

  Parameter ssubst_elift :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_elift e) v
       = cast_elift (ssubst n ss (cast_var x) e v).

  (** Abstract Reduction Properties *)

  Parameter astep_bind_1 :
    forall (e1 e2 ef:expr) (M1 M2:Memory.t) (x:var),
    let f := fun v => cast_eapp (cast_eabs x ef) v in
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
    try(destruct (hd_cons bs 0) ;
    specialize (IHe1 ((n + booker e2 0)%nat :: l)) ;
    specialize (IHe2 (n :: l)) ;
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

    destruct (hd_cons bs 0).
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
    try(destruct (hd_cons bs 0) ;
    specialize (IHe1 ((n + booker e2 0)%nat :: l)) ;
    specialize (IHe2 (n :: l)) ;
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
    
    destruct (hd_cons bs 0).
    specialize (IHe l).
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
    destruct H ; destruct (hd_cons bs1 0) ;
    destruct (hd_cons bs2 0) ; rewrite H, H0 in *|-* ;
    specialize (IHe1 nil (n + booker e2 0 :: l)%nat 
      (n0 + booker e2 0 :: l0)%nat Ole) ;
    specialize (IHe2 nil (n::l) (n0 :: l0) Ole) 
    | apply max_lub_iff in H ; destruct H ;
    specialize (IHe1 ((n + booker e2 0)%nat :: bs) bs1 bs2 H) ;
    specialize (IHe2 (n::bs) bs1 bs2 H0) ];
    simpl in *|-* ;
    rewrite IHe1, IHe2 ;
    reflexivity).

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
    svalue 0 v -> depth v = 0 -> phi v bs1 = phi v bs2.
  Proof.
    intros ; inversion H ; subst ; simpl in *|-* ; auto.
    rewrite trans_depth_0 with (bs2:=bs2) ; auto.
    rewrite trans_depth_0 with (bs2:=bs2) ; auto.
    rewrite trans_depth_0 with (bs2:=0 :: bs2) ; auto.
    apply CalculusProperties.depth_svalue in H1.
    omega.
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
  Import StaticProperties.
  Import Translation.
  Import M.S.
  Import M.

  (* Lemma context_stack_independent:
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
  *)

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
    destruct (hd_cons bs 0).
    specialize (IHe1 v ((n0 + booker e2 0)%nat :: l) x).
    specialize (IHe2 v (n0::l) x).
    destruct (trans e1) ; destruct (trans e2) ; intros.
    rewrite IHe2 ; auto ; clear IHe2.
    rewrite booker_ssubst ; [|auto].
    rewrite IHe1 ; auto ; clear IHe1.
    rewrite phi_depth_0 with (bs2:=nil) ; auto.
    rewrite phi_depth_0 with (bs1:=n0:: l) (bs2:=nil) ; auto.
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
    destruct (hd_cons bs 0).
    specialize (IHe1 v ((n0 + booker e2 0)%nat :: l) x).
    specialize (IHe2 v (n0::l) x).
    destruct (trans e1) ; destruct (trans e2) ; intros.
    rewrite IHe2 ; auto ; clear IHe2.
    rewrite booker_ssubst ; [|auto].
    rewrite IHe1 ; auto ; clear IHe1.
    rewrite phi_depth_0 with (bs2:=nil) ; auto.
    rewrite phi_depth_0 with (bs1:=n0:: l) (bs2:=nil) ; auto.
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
    destruct (hd_cons bs 0).
    specialize (IHe v l x).
    destruct (trans e) ; intros.
    rewrite IHe ; auto.
    rewrite MP.ssubst_eunbox ; auto.
    simpl.
    rewrite MP.ssubst_evar.
    assert(beq_nat (source_var x) (hole_var n0) &&
       CRaw.BindingSet.rho (pred n) ss = false).
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
    
    

  (*
  Fixpoint compose {T:Type} (n:nat) (f:T -> T) (x:T) : T :=
    match n with
    | 0 => x
    | S n => compose n f (f x)
    end.
  *)

  (* En gros, on distingue 2 mondes de variables:
    - les variables traduites (cast_var) qui sont celles 
   des expressions initiales et celles créées pour le contexte
    - les variables des opérateurs monadiques.
   On peut implémenter ça par une séparation par parité: cast_var
   enverrait n vers 2n, etles variables des opérateurs monadiques
   seraient 2n+1.
  *)
  Lemma sstep_rstep:
    forall (e1:S.expr) (bs:list nat) (e2:S.expr) (M1 M2:S.Memory.t),
    S.memory_depth M1 = 0 ->
    let n := depth e1 in
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
            admin_stack 
              (Context.ssubst_stack 
                 (pred n) StageSet.empty (hole_var h) (Context.unshift cs1' c1') 
                 (phi eh (0::nil))) cs2 /\
            admin
               (M.ssubst n StageSet.empty (M.cast_var (hole_var h)) e1' 
               (phi eh (0::nil))) e2'
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
    intros bs e2 M1 M2 MemDepth0 Step ; intros.

    (* Case EConst *)
    inversion Step.

    (* Case EVar *)
    inversion Step.

    (* Case EAbs *)
    inversion Step ; subst.
    rewrite <- H in IHe1.
    specialize (IHe1 bs e3 M1 M2 MemDepth0 H1).
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
      rewrite MP.ssubst_ret, MP.ssubst_eabs.
      apply Admin_ret, Admin_abs.
      assert(S.beq_var (hole_var v0) (source_var v) = false).
        apply beq_nat_false_iff.
        unfold hole_var, source_var.
        omega.
      simpl in *|-*.
      rewrite H2 ; assumption.

      (* Case not svalue *)
      exists x0.
      destruct H3 ; destruct H4 ; subst.
      auto.

    (* Case EFix *)
    inversion Step ; subst.
    rewrite <- H in IHe1.
    specialize (IHe1 bs e3 M1 M2 MemDepth0 H1).
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
      rewrite MP.ssubst_ret, MP.ssubst_efix.
      apply Admin_ret, Admin_fix.
      assert(orb (S.beq_var (hole_var v1) (source_var v)) 
          (S.beq_var (hole_var v1) (source_var v0)) = false).
        apply orb_false_intro ; apply beq_nat_false_iff ;
        unfold hole_var, source_var ; omega.
      simpl in *|-*.
      rewrite H2 ; assumption.
      exists x0.
      destruct H3 ; destruct H4 ; subst ; auto.

    (* Case EApp *)
    inversion Step ; subst ; simpl in *|-*.
    
      (* Case EApp e1 e2,  e1 -> e1' *)
      admit.

      (* Case EApp e1 e2,  e2 -> e2' *)
      admit.

      (* Case EApp (EAbs), n = 0 *)
      symmetry in H ; apply max_0 in H.
      destruct H.
      clear IHe1_2 IHe1_1.
      destruct (hd_cons bs 0).
      specialize (depth_length e ((n + booker e1_2 0)%nat :: l)) ; intros.
      assert(let (e0, _) := trans e ((n + booker e1_2 0)%nat :: l) in
      cast_eabs (cast_var (source_var x)) e0 = 
      phi (CRaw.EAbs x e) ((n + booker e1_2 0)%nat :: l)).
      simpl ; destruct (trans e) ; reflexivity.
      destruct (trans e).
      rewrite H3.
      rewrite H in H2 ; destruct t ; simpl in *|- ;
      [clear H2 |inversion H2].
      specialize (depth_length e1_2 (n :: l)) ; intros.
      specialize (svalue_phi e1_2 (n::l) H1) ; intros.
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
      rewrite phi_depth_0 with (bs2:=bs) ; auto.
      apply MP.astep_app_abs ; auto.
      omega.
      constructor.

      (* Case EApp (EFix), n = 0 *)
      admit.

    (* Case ELoc *)
    inversion Step.

    (* Case ERef *)
    fail.
    specialize (IHe1 acc).
    destruct (trans e1).
    intros.
    destruct t ; simpl in H ; intros ;
    inversion H ; subst.

      (* SubCase ERef, n=0, e -> e' *)
      specialize (IHe1 e3 M1 M2 MemDepth0 H2).
      unfold trans_expr.
      unfold trans_expr in IHe1.
      simpl.
      destruct (trans e3).
      simpl.
      admit.

    
      (* SubCase ERef, n=0, svalue 0 e *)
      simpl in *|-*.
      unfold trans_expr.
      simpl.
      admit.

      (* SubCase ERef, n>0 *)
      specialize (IHe1 e3 M1 M2 MemDepth0 H2).
      destruct (Context.shift (t :: t0)).
      destruct t1 ; simpl in *|-*.
        destruct (trans e3).
        destruct IHe1 ; subst ; tauto.
        assumption.

        destruct p ; destruct (trans e3) ; intros.
        specialize (IHe1 acc').
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
         (fun v2 => M.ssubst (S (length t0)) StageSet.empty (M.cast_var (hole_var v)) 
         (M.cast_eref v2) (phi x (compose (length t0) Injection.succ (Injection.succ acc)))) =
         (fun v2 => M.cast_eref (M.ssubst (S (length t0)) StageSet.empty 
         (M.cast_var (hole_var v)) v2 (phi x (compose (length t0) Injection.succ (Injection.succ acc)))))).
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
        specialize (IHe1 e3 M1 M2 MemDepth0 H5).
        destruct t.

          (* Case stack = [[]] Impossible *)
          exfalso ; assumption.
   
          (* Case stack = [a :: lst] *)
          destruct p ; clear H0.
          unfold trans_expr ; simpl.
          specialize (depth_length e3 acc) ; intros DL.
          destruct (trans e3) ; intros.
          specialize (IHe1 acc0).
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
            specialize (depth_length e3 acc0) ; intros DL2.
            rewrite DL in DL2.
            destruct (trans e3 acc0).
            simpl in DL2.
            destruct t0 ; simpl in *|-* ; [inversion DL2 | ].
            inversion DL2 ; subst ; destruct t1 ; simpl in *|-* ; [| inversion H0].
            clear DL2 H0.
            apply Rel_step with (e1:=Context.fill 
               (Context.ssubst_context 0 StageSet.empty (hole_var v) t (phi x (Injection.succ acc)))
               (M.ssubst 0 StageSet.empty (M.cast_var (hole_var v)) 
               (M.ret (M.cast_ebox e)) (phi x (Injection.succ acc))))
               (e2:=Context.fill k2 (ret (cast_ebox e2)))
               (M1:=trans_mem M2 acc0).
            assert(H10 := H3).
            apply svalue_phi with (acc:=(Injection.succ acc)) in H10.
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
            apply hole_rename_fill.
            constructor.

            (* Case not svalue *)
            destruct H3 ; destruct H3 ; destruct H4.
            subst.
            inversion H3 ; subst.
            simpl.
            apply Rel_step with (e1:=bind e0 (fun v0 =>
               cast_eapp
               (cast_eabs (cast_var (hole_var v))
               (Context.fill t (ret (cast_ebox e2)))) v0))
               (e2:=bind e4
               (fun v0 : T.expr =>
               cast_eapp (cast_eabs (cast_var (hole_var v))
               (Context.fill t (ret (cast_ebox e2)))) v0)).
            apply MP.astep_bind_1 ; assumption.
            constructor ;
            [assumption | intros ; constructor].
            constructor.
            assumption.

        (* Case of length(stack) > 1 *)
        admit.
        (*inversion H2 ; subst.
        specialize (IHe1 e3 M1 M2 MemDepth0 H5).
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
        simpl in *|-*.
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
          rewrite ssubst_fill_hole.
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
    *)

    (* Case EUnbox *)
    specialize (IHe1 (Injection.succ acc)).
    unfold trans_expr in *|-*.
    assert(trans e1 (Injection.succ acc)  = 
        (trans ((fun x => x) e1) (Injection.succ acc) )).
    reflexivity.
    destruct (trans e1).
    (*destruct (trans e1 (Injection.succ acc)).*)
    simpl in *|-* ; intros.
   (*  assert(length t0 = length t).
    admit. (* TODO, but easily provable *)
    rewrite H1 in *|-*. 
*)

    inversion H0 ; subst.

      (* Case EUnbox -> EUnbox *)
      specialize (IHe1 e3 M1 M2 MemDepth0 H3).
      destruct t.

        (* Case n = 1 *)
        unfold trans_expr in *|-*.
        simpl in *|-*.
        (*destruct t ; simpl in H1 ; [|inversion H1] ; clear H1. *)
        assert(trans e3 (Injection.succ acc)  = 
          (trans ((fun x => x) e3) (Injection.succ acc))).
        reflexivity.
        destruct (trans e3).
        (*destruct (trans e4 (Injection.succ acc)).*)
        exists e1.
        split.
        destruct (trans e1) ; inversion H ; subst ; auto.
      
        right.
        exists e3.
        repeat (split ; auto).
        
        destruct (trans e3) ; inversion H1 ; subst ; auto.

        assert(depth e1 = 0).
        specialize (depth_length e1 (Injection.succ acc)) ; intros.
        destruct (trans e1).
        inversion H ; subst ; auto.
        assert(t = nil).
        specialize (length_sstep e1 e3 M1 M2 (Injection.succ acc)) ; intros.
        rewrite H2 in *|-* ; specialize (H4 H3 MemDepth0).
        destruct (trans e3).
        apply le_n_0_eq in H4.
        inversion H1 ; subst.
        destruct t0 ; [auto | inversion H4].
        subst.
        destruct (trans e3) ; inversion H1 ; subst ; auto.

        (* Case n > 1 *)
        destruct (Context.shift (t :: t0)).
        destruct t1 ; simpl in *|-*.
        assumption.

        destruct p ; destruct (trans e3).
        destruct IHe1.
        exists x.
        destruct H1 ; split ; [assumption|].
        destruct H2 ; [left | right] ; destruct H2.

          (* Case svalue *)
          destruct H4 ; destruct H5.
          repeat(split ; auto).
          constructor.
          assumption.
          constructor.
          constructor.
          assumption.
          
          (* Case not svalue *)
          

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
        fail.

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
    memory_depth M1 = 0 ->
    S.sstep 0 (M1, e1) (M2, e2) -> 
    rstep (trans_mem M1 acc, trans_expr e1 acc) 
      (trans_mem M2 acc, trans_expr e2 acc).
  Proof.
    intros.
    specialize (sstep_rstep e1 acc e2 M1 M2 H0) ; intros.

    assert(forall (e1':T.expr) (cs1:Context.t_stack), 
    trans e1 acc = (e1', cs1) -> cs1 = nil).
    intros.
      assert(0 = length cs1).
      rewrite <- H.
      specialize (depth_length e1) ; intros.
      specialize (H4 acc) ;
      rewrite H3 in H4 ; destruct H4.
      reflexivity.
    destruct cs1 ; simpl in *|-* ;
    [reflexivity | inversion H4].

    unfold trans_expr in *|-*.
    destruct (trans e1).
    specialize (H3 e t).
    rewrite H3 in H2.
    simpl in H2.
    destruct (trans e2).
    auto.
    auto.
  Qed.

End TranslationProperties.
