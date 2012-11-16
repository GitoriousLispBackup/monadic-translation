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
    | c :: cs => (ssubst_context (pred n) ss x c v) ::
       (ssubst_stack n ss x cs v)
    end.

End Context.

(* Translation R T <: StagedTranslation (Calculus R) T. *)
Module Translation (R:Replacement) 
    (T:StagedCalculus) (M:Monad R T). 

  Module S := M.S.
  Module Context := Context R T M.
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

  Definition phi (e:S.expr) : T.expr :=
    match e with
    | EConst i => M.cast_econst i
    | EVar y => M.cast_evar (M.cast_var (source_var y))
    | EAbs y e => 
        let (e, _) := trans e in
        M.cast_eabs (M.cast_var (source_var y)) e
    | EFix f y e => 
        let (e, _) := trans e in
        M.cast_efix 
            (M.cast_var (source_var f)) 
            (M.cast_var (source_var y)) e
    | ELoc l => M.cast_eloc l
    | EBox e => 
        let (e, _) := trans e in
        M.cast_ebox e
    | _ => M.cast_econst 0
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
    | Admin_app : forall (e1 e2 e3 e4:T.expr),
        admin e1 e3 -> admin e2 e4 -> 
        admin (M.cast_eapp e1 e2) (M.cast_eapp e3 e4)
    | Admin_ret : forall (e1 e2:T.expr),
        admin e1 e2 -> admin (M.ret e1) (M.ret e2)
    | Admin_bind : forall (e1 e2:T.expr) (f1 f2:T.expr -> T.expr),
        admin e1 e2 -> (forall e3:T.expr, admin (f1 e3) (f2 e3)) ->
        admin (M.bind e1 f1) (M.bind e2 f2)
    | Admin_reduc : forall e:expr, svalue 1 e ->
        admin (M.cast_eunbox (M.cast_ebox (trans_expr e))) (trans_expr e).

  Definition admin_context : relation Context.t := 
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

  (** Abstract Reduction Properties *)

  Parameter astep_ssubst_1 :
    forall (v:S.expr) (e:expr) (M1 M2:Memory.t) (f:expr -> expr),
    S.svalue 0 v -> astep (M1, (f (phi v))) (M2, e) ->
    astep (M1, (bind (ret (phi v)) f)) (M2, e).

End MonadProperties.

Module ContextProperties (R:Replacement) (T:StagedCalculus) 
    (M:Monad R T) (MP:MonadProperties R T M).

  Module Context := Context R T M.
  Import MP.Translation.
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

  Lemma fill_ssubst:
    forall (c:t) (n:nat) (ss:StageSet.t) (x:S.var) (v:S.expr) (e:T.expr),
    S.svalue 0 v -> VarSet.mem x (context_hole_set c) = false ->
      fill (ssubst_context n ss x c (ret (phi v))) 
      (ssubst n ss (M.cast_var (hole_var x)) e (ret (phi v))) = 
      ssubst n ss (cast_var (hole_var x)) (fill c e) (ret (phi v)).
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
        (ssubst n ss (cast_var (hole_var x)) (fill c e) (ret (phi v)))) v1)).
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

Module TranslationProperties (R:Replacement) 
    (T:StagedCalculus) (M:Monad R T) (MP:MonadProperties R T M). 

  Module Translation := MP.Translation.
  Module ContextProperties := ContextProperties R T M MP.
  Module CalculusProperties := CalculusProperties R M.S.
  Import Translation.
  Import M.S.
  Import M.

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
    apply Admin_app.
    apply Admin_abs.
    apply IHk1 ; [ assumption | assumption ].
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

  Lemma svalue_phi:
    forall (e:expr),
    svalue 0 e -> trans_expr e = M.ret (phi e).
  Proof.
    intros ; inversion H ; subst ; simpl ;
    try(reflexivity) ;
    try(unfold trans_expr ; simpl ; 
    destruct (trans e0) ; reflexivity).

    unfold trans_expr.
    simpl.
    inversion H ; subst.
    specialize (length_svalue e0 0) ; intros.
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
    forall (e:expr),
    let (_, cs) := trans e in
    ~ In nil cs.
  Proof.
    intros ;
    induction e ; simpl ; auto ;

    try( destruct (trans e) ; auto ; fail) ;

    try(destruct (trans e1) ; destruct (trans e2 ) ;
    unfold not ; intros ;
    apply context_merge_not_nil in H ;
    tauto ; fail).

    destruct (trans e).
    destruct t ; simpl.
    tauto.
    unfold not ; intros ; apply IHe.
    simpl ; auto.
    
    destruct (trans e).
    unfold not ; intros ; apply IHe.
    simpl in *|-*.
    destruct H.
    inversion H.
    assumption.
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
      | cons (t_eh, h) c1' => 
          let (e2', cs2) := trans e2 in
          let M1' := trans_mem M1 in
          let M2' := trans_mem M2 in
          exists eh, 
          (
            S.svalue 0 eh /\ 
            t_eh = trans_expr eh /\ 
            M1 = M2 /\ 
            admin_stack 
              (Context.ssubst_stack 
                 (pred n) StageSet.empty h (c1' :: cs1') t_eh) cs2 /\
            admin
               (M.ssubst n StageSet.empty (M.cast_var (hole_var h)) e1' t_eh) e2'
          \/ 
            exists eh', let t_eh' := trans_expr eh' in
            rstep (M1', t_eh) (M2', t_eh') /\
            cs2 = ((t_eh', h) :: c1') :: cs1'
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
      exists x.
      destruct H0 ; [left | right] ;
      destruct H0.
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

      simpl in H1.
      rewrite H1 ; assumption.
      exists x0.
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
      exists x.
      destruct H0 ; [left | right] ; destruct H0.
      destruct H1 ; destruct H3 ; destruct H4.
      subst.
      repeat(split ; auto).

      rewrite MP.ssubst_ret, MP.ssubst_efix.
      apply Admin_ret, Admin_fix.

      assert(orb (S.beq_var (hole_var v1) (source_var v)) 
          (S.beq_var (hole_var v1) (source_var v0)) = false).
        apply orb_false_intro ; apply beq_nat_false_iff ;
        unfold hole_var, source_var ; omega.

      simpl in H1.
      rewrite H1 ; assumption.
      exists x0.
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
        exists x.
        destruct H0 ; [left | right] ; destruct H0.
        destruct H1 ; destruct H3 ; destruct H4.
        repeat(split ; auto).

        rewrite MP.ssubst_bind with (f2:=(fun v0 : T.expr => cast_eref v0)).
        apply Admin_bind.
        assumption.
        intros.
        apply Admin_refl.

        assert (
         (fun v2 => M.ssubst (S (length t0)) StageSet.empty (M.cast_var (hole_var v)) (M.cast_eref v2) e0) =
         (fun v2 => M.cast_eref (M.ssubst (S (length t0)) StageSet.empty (M.cast_var (hole_var v)) v2 e0))).
          apply functional_extensionality.
          intros ; apply MP.ssubst_eref.
        assumption.
        exists x0.
        assumption.

    (* Case EDeref *)
    admit.

    (* Case EAssign *)
    admit.

    (* Case EBox *)
    
    specialize (length_svalue e1 0) ; intros.
    specialize (context_stack_not_nil e1) ; intros.
    destruct (trans e1).
    destruct t ; simpl in *|-* ; intros.

      (* Case of empty stack. Impossible *)
      inversion H1 ; subst ; simpl in *|-*.
      destruct H.
      assert(svalue 1 e1).
      apply H ; omega.
      specialize (CalculusProperties.svalue_not_sprogresses 1 M1 e1 H3 (M2,e3) H4) ; intros.
      contradiction.

      (* Case of stack > 0 *)
      destruct t0 ; simpl in *|-*.

        (* Case of length(stack) = 1 *)
        inversion H1 ; subst ; simpl in *|-*.
        specialize (IHe1 e3 M1 M2 H4).
        destruct t.

          (* Case stack = [[]] Impossible *)
          exfalso ; apply H0 ; left ; reflexivity.
   
          (* Case stack = [a :: lst] *)
          destruct p ; clear H0.
          destruct (trans e3).
          destruct IHe1.
          destruct H0.

            (* Case svalue *)
            destruct H0 ; destruct H2 ; 
            destruct H3 ; destruct H5.
            subst.
            clear H.
            inversion H5 ; subst.
            inversion H3 ; subst ; clear H5 H3.
            simpl.
            admit.

(*
            apply Rel_step with (e1:=Context.fill 
               (Context.ssubst_context 0 StageSet.empty v t (trans_expr x))
               (M.ssubst 0 StageSet.empty (M.cast_var (hole_var v)) 
               (M.ret (M.cast_ebox e)) (trans_expr x))).
            assert(H9 := H0).
            apply svalue_phi in H9.
            rewrite H9. 
            apply MP.astep_ssubst_1.
            assumption.
            rewrite ContextProperties.fill_ssubst.

            (* To prove *)
            fail.*)

            (* Case not svalue *)
            admit.

        (* Case of length(stack) > 1 *)
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
