Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.MinMax.
Require Import Coq.Bool.Bool.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import "Misc/Library".
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

  (** Substitution Properties *)
  Parameter ssubst_ret :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (ret e) v = ret (ssubst n ss (cast_var x) e v).

  Parameter ssubst_bind :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e1 v:expr) (e2: expr -> expr),
     ((fun v2 => ssubst n ss (cast_var x) (e2 v2) v) = 
       fun v2 => e2 (ssubst n ss (cast_var x) v2 v)) ->
     ssubst n ss (cast_var x) (bind e1 e2) v = 
       bind (ssubst n ss (cast_var x) e1 v) e2.

(*  Parameter ssubst_bind_2 :
    forall (n:nat) (ss:StageSet.t) (x:var) (e1 v:expr) (e2: expr -> expr),
     ssubst n ss x (bind e1 e2) v = 
       bind e1 (fun v2 => e2 (ssubst n ss x v2 v)).*)

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

  Parameter ssubst_eref :
    forall (n:nat) (ss:StageSet.t) (x:S.var) (e v:expr),
     ssubst n ss (cast_var x) (cast_eref e) v
       = cast_eref (ssubst n ss (cast_var x) e v).

End Monad.


Module Context (R:Replacement) (T:StagedCalculus) (M:Monad R T).

  Import T.

  Definition t : Type := list (expr * M.S.var).
  Definition t_stack : Type := list t.

  Definition empty : list t := nil.

  Fixpoint fill (c:t) (e:expr) :=
    match c with
    | nil => e
    | (e1, x) :: c => M.bind e1 (fun v => 
            M.cast_eabs (M.cast_var (hole_var x)) (fill c v))
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

End Context.

Module ContextProperties (R:Replacement) (T:StagedCalculus) (M:Monad R T).

  Module Context := Context R T M.
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

End ContextProperties.

Module ContextExtensions (R:Replacement) (T:StagedCalculus) (M:Monad R T).

  Module Context := Context R T M.
  Import Context.
  Import T.

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
    | c :: cs => (ssubst_context (pred n) ss x c v) ::
       (ssubst_stack n ss x cs v)
    end.

End ContextExtensions.

(* Translation R T <: StagedTranslation (Calculus R) T. *)
Module Translation (R:Replacement) 
    (T:StagedCalculus) (M:Monad R T). 

  Module S := M.S.
  Module Context := Context R T M.
  Module ContextExtensions := ContextExtensions R T M.
  Import S.CRaw.

  Fixpoint trans (e:S.expr) : T.expr * Context.t_stack :=
    match e with
    | EConst i => (M.ret (M.cast_econst i), Context.empty)
    | EVar y => (M.ret (M.cast_evar (M.cast_var (source_var y))), Context.empty)
    | EAbs y e => 
        let (e,cs) := trans e in
        (M.ret (M.cast_eabs (M.cast_var (source_var y)) e), cs)
    | EFix f y e => 
        let (e,cs) := trans e in
        (M.ret (M.cast_efix 
            (M.cast_var (source_var f)) 
            (M.cast_var (source_var y)) e), cs)
    | EApp e1 e2 => 
        let (e1, cs1) := trans e1 in
        let (e2, cs2) := trans e2 in
        (M.bind e1
        (fun v1 => M.bind e2
        (fun v2 => M.cast_eapp v1 v2)), 
        Context.merge cs1 cs2)
    | ELoc l => (M.ret (M.cast_eloc l), Context.empty)
    | ERef e => 
        let (e,cs) := trans e in
        (M.bind e (fun v => M.cast_eref v), cs)
    | EDeref e => 
        let (e,cs) := trans e in
        (M.bind e (fun v => M.cast_ederef v), cs)
    | EAssign e1 e2 =>
        let (e1, cs1) := trans e1 in
        let (e2, cs2) := trans e2 in
        (M.bind e1
        (fun v1 => M.bind e2
        (fun v2 => M.cast_eassign v1 v2)), 
        Context.merge cs1 cs2)
    | EBox e => 
        let (e, cs) := trans e in
        match cs with
        | nil => (M.ret (M.cast_ebox e), Context.empty)
        | c :: cs => (Context.fill c (M.ret (M.cast_ebox e)), cs)
        end
    | EUnbox e =>
       let (e', cs) := trans e in
       let h := M.S.fresh e in
       (M.cast_eunbox (M.cast_evar (M.cast_var (hole_var h))), ((e', h) :: nil) :: cs)
    | ERun e =>
        let (e,cs) := trans e in
        (M.bind e (fun v => M.cast_erun v), cs)
    | ELift e =>
        let (e,cs) := trans e in
        (M.bind e (fun v => M.cast_elift v), cs)
    end.

  Definition trans_expr (e:S.expr) : T.expr :=
    let (e, _) := trans e in e.

  Fixpoint trans_mem (m:S.Memory.t) : T.Memory.t :=
    match m with
    | nil => nil
    | e :: m => trans_expr e :: (trans_mem m)
    end.


  (** ** Administrative Reduction Step *)
  (* TODO: Not finished yet *)
  Inductive admin: relation T.expr :=
    | Admin_refl : forall (e:T.expr), admin e e
    | Admin_trans : forall (e1 e2 e3:T.expr), 
        admin e1 e2 -> admin e2 e3 -> admin e1 e3
    | Admin_abs : forall (x:T.var) (e1 e2:T.expr),
        admin e1 e2 -> admin (M.cast_eabs x e1) (M.cast_eabs x e2)
    | Admin_fix : forall (f x:T.var) (e1 e2:T.expr),
        admin e1 e2 -> admin (M.cast_efix f x e1) (M.cast_efix f x e2)
    | Admin_ret : forall (e1 e2:T.expr),
        admin e1 e2 -> admin (M.ret e1) (M.ret e2)
    | Admin_bind : forall (e1 e2:T.expr) (f1 f2:T.expr -> T.expr),
        admin e1 e2 -> (forall e3:T.expr, admin (f1 e3) (f2 e3)) ->
        admin (M.bind e1 f1) (M.bind e2 f2)
    | Admin_reduc : forall e:expr, svalue 1 e ->
        admin (M.cast_eunbox (M.cast_ebox (trans_expr e))) (trans_expr e).

  Definition admin_context : relation Context.t := 
    ContextExtensions.congr_context admin.
  Definition admin_stack : relation Context.t_stack := 
    ContextExtensions.congr_stack admin.

  (** ** Relative Abstract Reduction Step *)
  Inductive rstep : relation T.state :=
    | Rel_step : forall (s:T.state) (e1 e2:T.expr) (M:T.Memory.t),
        M.astep s (M,e1) -> admin e1 e2 -> rstep s (M,e2).

End Translation.

Module TranslationProperties (R:Replacement) 
    (T:StagedCalculus) (M:Monad R T). 

  Module Translation := Translation R T M.
  Module ContextProperties := ContextProperties R T M.
  Module CalculusProperties := CalculusProperties R.
  Import Translation.
  Import M.S.

  Lemma admin_context_expr:
    forall (k1 k2:Context.t) (e1 e2:T.expr),
    admin_context k1 k2 -> admin e1 e2 ->
    admin (Context.fill k1 e1) (Context.fill k2 e2).
  Proof.
    unfold admin_context ;
    induction k1 ; intros.
    inversion H ; subst.
    simpl ; assumption.

    destruct a ; inversion H ; subst.
    simpl ; apply Admin_bind ; 
    [assumption | intros].
    apply Admin_abs.
    apply IHk1 ; [ assumption | apply Admin_refl ].
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
    simpl ; apply ContextExtensions.CongrCtx_cons.
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
     apply ContextExtensions.CongrStack_context.
     apply IHcs1 ; assumption.
     apply admin_context_context ;
     [inversion H | inversion H0] ; subst ;
     assumption.
  Qed.

  Lemma depth_length:
    forall e:expr,
    let (_, cs) := trans e in
    depth e = length cs.
  Proof.
    induction e ; simpl ; intros ;
    try(auto ; fail) ;
    try(destruct (trans e) ; auto) ;
    try(destruct (trans e1) ; destruct (trans e2) ;
    simpl ; rewrite ContextProperties.merge_length ; auto).

    destruct (depth e) ; destruct t ; simpl in *|-*.
    reflexivity.
    inversion IHe.
    inversion IHe.
    auto.

    simpl ; auto.
  Qed.

  Lemma length_svalue:
    forall (e:expr) (n:nat),
    let (_, cs) := trans e in
    length cs < (S n) <-> svalue (S n) e.
  Proof.
    intros.
    specialize (depth_length e) ; intros.
    destruct (trans e).
    rewrite <- H.
    apply CalculusProperties.depth_svalue.
  Qed.

  (*Inductive indep_context_vars (e:expr) : Context.t -> Type :=
    | IndepContextVars_nil : indep_context_vars e nil
    | IndepContextVars_cons : forall (h:var) (eh:expr) (c:Context.t), vars e x 

  Inductive indep_stack_vars (e:expr) : Context.t_stack -> Type :=
    | IndepStackVars_nil : indep_stack_vars e nil
    | IndepStackVars_cons : forall (c:Context.t) (cs:Context.t_stack),
        indep_context_vars e c -> indep_stack_vars e cs -> 
        indep_stack_vars e cs.*)

  (*Lemma trans_indep_stack: .*)

  (* En gros, on distingue 2 mondes de variables:
    - les variables traduites (cast_var) qui sont celles 
   des expressions initiales et celles créées pour le contexte
    - les variables des opérateurs monadiques.
   On peut implémenter ça par une séparation par parité: cast_var
   enverrait n vers 2n, etles variables des opérateurs monadiques
   seraient 2n+1.
  *)
  Lemma sstep_rstep:
    forall (e1 e2:S.expr) (M1 M2:S.Memory.t),
    let (e1', cs1) := trans e1 in
    let n := length cs1 in
    S.sstep n (M1, e1) (M2, e2) -> 
    match cs1 with
    | nil => rstep (trans_mem M1, e1') (trans_mem M2, trans_expr e2)
    | cs1 => let (c1, cs1') := Context.shift cs1 in
      match c1 with
      | nil => 
          let (e2', cs2) := trans e2 in 
          e1' = e2' /\ M1 = M2 /\ cs1 = cs2
      | cons (eh, h) c1' => 
          let (e2', cs2) := trans e2 in
          let M1' := trans_mem M1 in
          let M2' := trans_mem M2 in
          (T.svalue 0 eh ->
            M1 = M2 /\ 
            admin_stack 
              (ContextExtensions.ssubst_stack 
                 (pred n) StageSet.empty h (c1' :: cs1') eh) cs2 /\
            admin
               (M.ssubst n StageSet.empty (M.cast_var (hole_var h)) e1' eh) e2'
          ) /\
          (~T.svalue 0 eh -> exists eh',
            rstep (M1', eh) (M2', eh') /\
            cs2 = ((eh', h) :: c1') :: cs1')
      end
    end.
  Proof.
    induction e1 ; simpl ; intros.

    (* Case EConst *)
    inversion H.

    (* Case EVar *)
    inversion H.

    (* Case EAbs *)
    destruct (trans e1).
    intros.

    destruct t ; simpl in H;
    inversion H ; subst.
    specialize (IHe1 e3 M1 M2 H2).
    destruct (Context.shift (t :: t0)).
    destruct t1 ; simpl in *|-*.
      destruct (trans e3).
      destruct IHe1 ; subst ; tauto.

      destruct p ; destruct (trans e3).
      destruct IHe1.
      split ; intros ; [specialize (H0 H3) | specialize (H1 H3)].
      destruct H0 ; subst.
      destruct H4.
      split ; [trivial|].
      split ; [trivial|].

      rewrite M.ssubst_ret, M.ssubst_eabs.
      apply Admin_ret, Admin_abs.

      assert(S.beq_var (hole_var v0) (source_var v) = false).
        apply beq_nat_false_iff.
        unfold hole_var, source_var.
        omega.

      simpl in H5.
      rewrite H5 ; assumption.
      assumption.


    (* Case EFix *)
    destruct (trans e1).
    intros.

    destruct t ; simpl in H;
    inversion H ; subst.
    specialize (IHe1 e3 M1 M2 H2).
    destruct (Context.shift (t :: t0)).
    destruct t1 ; simpl in *|-*.
      destruct (trans e3).
      destruct IHe1 ; subst ; tauto.

      destruct p ; destruct (trans e3).
      destruct IHe1.
      split ; intros ; [specialize (H0 H3) | specialize (H1 H3)].
      destruct H0 ; subst.
      destruct H4.
      split ; [trivial|].
      split ; [trivial|].

      rewrite M.ssubst_ret, M.ssubst_efix.
      apply Admin_ret, Admin_fix.

      assert(orb (S.beq_var (hole_var v1) (source_var v)) 
          (S.beq_var (hole_var v1) (source_var v0)) = false).
        apply orb_false_intro ; apply beq_nat_false_iff ;
        unfold hole_var, source_var ; omega.

      simpl in H5.
      rewrite H5 ; assumption.

      assumption.

    (* Case EApp *)
    admit.

    (* Case ELoc *)
    inversion H.

    (* Case ERef *)
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

        destruct p ; destruct (trans e3).
        destruct IHe1.
        split ; intros ; [specialize (H0 H3) | specialize (H1 H3)].
        destruct H0 ; subst.
        destruct H4.
        split ; [trivial|].
        split ; [trivial|].

        rewrite M.ssubst_bind.
        apply Admin_bind.
        assumption.
        intros.
        apply Admin_refl.

        assert (
         (fun v2 => M.ssubst (S (length t0)) StageSet.empty (M.cast_var (hole_var v)) (M.cast_eref v2) e0) =
         (fun v2 => M.cast_eref (M.ssubst (S (length t0)) StageSet.empty (M.cast_var (hole_var v)) v2 e0))).
          apply functional_extensionality.
          intros ; apply M.ssubst_eref.
        assumption.
        assumption.

    (* Case EDeref *)
    admit.

    (* Case EAssign *)
    admit.

    (* Case EBox *)
    admit.

    (* Case EUnbox *)
    admit.

    (* Case ERun *)
    admit.

    (* Case ELift *)
    admit.
  Qed.

  Theorem sstep_rstep_O:
    forall (e1 e2:S.expr) (M1 M2:S.Memory.t),
    depth e1 = 0 ->
    S.sstep 0 (M1, e1) (M2, e2) -> 
    rstep (trans_mem M1, trans_expr e1) (trans_mem M2, trans_expr e2).
  Proof.
    intros.
    specialize (sstep_rstep e1 e2 M1 M2) ; intros.

    assert(forall (e1':T.expr) (cs1:Context.t_stack), 
    trans e1 = (e1', cs1) -> cs1 = nil).
    intros.
      assert(0 = length cs1).
      rewrite <- H.
      specialize (depth_length e1) ; intros.
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