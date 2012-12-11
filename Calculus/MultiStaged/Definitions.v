Require Import Coq.Relations.Relations.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.MinMax.
Require Import Coq.Arith.NatOrderedType.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Compare_dec.
Require Import "Calculus/Sets".
Require Import "Calculus/Definitions".

Module CalculusData.

  (** ** Sets *)
  Definition var : Set := nat.
  Definition const : Set := nat.
  Definition location : Set := nat.

  Definition beq_var := beq_nat.

  (** ** Terms *)
  Inductive expr : Set :=
   | EConst : const -> expr
   | EVar : var -> expr
   | EAbs : var -> expr -> expr
   | EFix : var -> var -> expr -> expr
   | EApp : expr -> expr -> expr
   | ELoc : location -> expr
   | ERef : expr -> expr
   | EDeref : expr -> expr
   | EAssign : expr -> expr -> expr
   | EBox : expr -> expr
   | EUnbox : expr -> expr
   | ERun : expr -> expr
   | ELift : expr -> expr.

  Inductive complexity : nat -> expr -> Prop :=
    | Compl_const : forall (c:const), complexity 0 (EConst c)
    | Compl_var : forall (x:var), complexity 0 (EVar x)
    | Compl_abs : forall (n:nat) (x:var) (e:expr), 
        complexity n e -> complexity (S n) (EAbs x e)
    | Compl_fix : forall (n:nat) (f x:var) (e:expr), 
        complexity n e -> complexity (S n) (EFix f x e)
    | Compl_app : forall (m n:nat) (e1 e2:expr), 
        complexity m e1 -> complexity n e2 ->
	complexity (S (max m n)) (EApp e1 e2)
    | Compl_loc : forall (l:location), complexity 0 (ELoc l)
    | Compl_ref : forall (n:nat) (e:expr), 
        complexity n e -> complexity (S n) (ERef e)
    | Compl_deref : forall (n:nat) (e:expr), 
        complexity n e -> complexity (S n) (EDeref e)
    | Compl_assign : forall (m n:nat) (e1 e2:expr), 
        complexity m e1 -> complexity n e2 ->
	complexity (S (max m n)) (EAssign e1 e2)
    | Compl_box : forall (n:nat) (e:expr), 
        complexity n e -> complexity (S n) (EBox e)
    | Compl_unbox : forall (n:nat) (e:expr),
        complexity n e -> complexity (S n) (EUnbox e)
    | Compl_run : forall (n:nat) (e:expr),
        complexity n e -> complexity (S n) (ERun e)
    | Compl_lift : forall (n:nat) (e:expr),
        complexity n e -> complexity (S n) (ELift e).

  (** ** Values *)
  Inductive svalue : nat -> expr -> Prop :=
    | EVal_const : forall (n:nat) (c:const), svalue n (EConst c)
    | EVal_var : forall (n:nat) (x:var), svalue n (EVar x)
    | EVal_abs : forall (n:nat) (x:var) (e:expr), 
        svalue (S n) e -> svalue (S n) (EAbs x e)
    | EVal_abs_O : forall (x:var) (e:expr), svalue 0 (EAbs x e)
    | EVal_fix : forall (n:nat) (f x:var) (e:expr), 
        svalue (S n) e -> svalue (S n) (EFix f x e)
    | EVal_fix_O : forall (f x:var) (e:expr), svalue 0 (EFix f x e)
    | EVal_app : forall (n:nat) (e1 e2:expr), 
        svalue (S n) e1 -> svalue (S n) e2 -> svalue (S n) (EApp e1 e2)
    | EVal_loc : forall (n:nat) (l:location), svalue n (ELoc l)
    | EVal_ref : forall (n:nat) (e:expr), 
        svalue (S n) e -> svalue (S n) (ERef e)
    | EVal_deref : forall (n:nat) (e:expr), 
        svalue (S n) e -> svalue (S n) (EDeref e)
    | EVal_assign : forall (n:nat) (e1 e2:expr), 
        svalue (S n) e1 -> svalue (S n) e2 -> svalue (S n) (EAssign e1 e2)
    | EVal_box : forall (n:nat) (e:expr), 
        svalue (S n) e -> svalue n (EBox e)
    | EVal_unbox : forall (n:nat) (e:expr),
        svalue (S n) e -> svalue (S (S n)) (EUnbox e)
    | EVal_run : forall (n:nat) (e:expr),
        svalue (S n) e -> svalue (S n) (ERun e)
    | EVal_lift : forall (n:nat) (e:expr),
        svalue (S n) e -> svalue (S n) (ELift e).

  Fixpoint svalueb (n:nat) (e:expr) : bool :=
    match e with
    | EConst _ => true
    | EVar _ => true
    | EAbs _ e => beq_nat n 0 || svalueb n e
    | EFix _ _ e => beq_nat n 0 || svalueb n e
    | EApp e1 e2 => (leb 1 n) && svalueb n e1 && svalueb n e2
    | ELoc _ => true
    | ERef e => (leb 1 n) && svalueb n e
    | EDeref e => (leb 1 n) && svalueb n e
    | EAssign e1 e2 => (leb 1 n) && svalueb n e1 && svalueb n e2
    | EBox e => svalueb (S n) e
    | EUnbox e => (leb 2 n) && svalueb (pred n) e
    | ERun e => (leb 1 n) && svalueb n e
    | ELift e => (leb 1 n) && svalueb n e
    end.

  (** ** Memory **)
  Module MemoryType <: MemoryType.
    Definition data := expr.
    Definition default := EConst 0.
  End MemoryType.
  Module Memory := Memory MemoryType.

  Inductive memory_svalue (n:nat) : Memory.t -> Prop :=
    | MSValue_nil : memory_svalue n nil
    | MSValue_cons : forall (e:expr) (M:Memory.t), 
	svalue n e -> memory_svalue n M -> memory_svalue n (cons e M).

End CalculusData.

(** * Raw Calculus *)
Module CalculusRaw (Repl:Replacement).

  (** ** Parameters *)
  Include Repl.
  Include CalculusData.

  (** ** Sticks *)
  (** TODO: Dummy implementation *)
  Definition ssticks (n:nat) (e:expr) := True.

  (** ** Binding Set *)
  Module BindingSet := BindingSet Repl.

  (** ** Substitution *)
  Fixpoint ssubst (n:nat) (St:StageSet.t) (x:var) (e v:expr) :=
    match e with
    | EConst _ => e
    | EVar y =>  
        if andb (beq_nat x y) (BindingSet.rho n St) 
        then v else EVar y
    | EAbs y e => EAbs y (ssubst n 
        (if beq_nat x y 
        then (StageSet.add n St) else St) x e v)
    | EFix f y e => EFix f y (ssubst n 
        (if orb (beq_nat x f) (beq_nat x y) 
        then (StageSet.add n St) else St) x e v)
    | EApp e1 e2 => EApp (ssubst n St x e1 v) (ssubst n St x e2 v)
    | ELoc l => ELoc l
    | ERef e => ERef (ssubst n St x e v)
    | EDeref e => EDeref (ssubst n St x e v)
    | EAssign e1 e2 => EAssign (ssubst n St x e1 v) (ssubst n St x e2 v)
    | EBox e => EBox (ssubst (S n) St x e v)
    | EUnbox e => EUnbox (ssubst (pred n) (StageSet.remove n St) x e v)
    | ERun e => ERun (ssubst n St x e v)
    | ELift e => ELift (ssubst n St x e v)
  end.

  Definition state : Type := Memory.t * expr.
  Notation "'⟨' M ',' e '⟩'" := ((M, e):state) (at level 40).

  (** ** Operational Semantics *)

  (** *** Structural Semantics *)

  Reserved Notation "s1 '⊨' n '⇒' s2" (at level 40).

  Inductive sstep : nat -> relation state :=
    | EStep_abs : forall (n:nat) (M N:Memory.t) (x:var) (e1 e2:expr),
       ⟨M, e1⟩ ⊨ S n ⇒ (N, e2) -> ⟨M, EAbs x e1⟩ ⊨ S n ⇒ ⟨N, EAbs x e2⟩
    | EStep_fix : forall (n:nat) (M N:Memory.t) (f x:var) (e1 e2:expr),
       ⟨M, e1⟩ ⊨ S n ⇒ (N, e2) -> ⟨M, EFix f x e1⟩ ⊨ S n ⇒ ⟨N, EFix f x e2⟩
    | EStep_app_l : forall (n:nat) (M N:Memory.t) (e1 e2 e3:expr), 
       ⟨M, e1⟩ ⊨ n ⇒ (N, e3) -> ⟨M, EApp e1 e2⟩ ⊨ n ⇒ ⟨N, EApp e3 e2⟩
    | EStep_app_r : forall (n:nat) (M N:Memory.t) (v e1 e2:expr),
       svalue n v -> ⟨M, e1⟩ ⊨ n ⇒ (N, e2) -> 
       ⟨M, EApp v e1⟩ ⊨ n ⇒ ⟨N, EApp v e2⟩
    | EStep_app_abs : forall (M:Memory.t) (x:var) (e v:expr), svalue 0 v -> 
       ⟨M, EApp (EAbs x e) v⟩ ⊨ 0 ⇒ ⟨M, ssubst 0 StageSet.empty x e v⟩
    | EStep_app_fix : forall (M:Memory.t) (f x:var) (e v:expr), 
       svalue 0 v -> ⟨M, EApp (EFix f x e) v⟩ ⊨ 0 ⇒ 
       ⟨M, ssubst 0 StageSet.empty f 
         (ssubst 0 StageSet.empty x e v) (EFix f x e)⟩
    | EStep_ref : forall (n:nat) (M N:Memory.t) (e1 e2:expr),
       ⟨M, e1⟩ ⊨ n ⇒ (N, e2) -> ⟨M, ERef e1⟩ ⊨ n ⇒ ⟨N, ERef e2⟩
    | EStep_ref_O : forall (M:Memory.t) (v:expr),
       svalue 0 v -> ⟨M, ERef v⟩ ⊨ 0 ⇒
         ⟨Memory.set (Memory.fresh M) v M, ELoc (Memory.fresh M)⟩
    | EStep_deref : forall (n:nat) (M N:Memory.t) (e1 e2:expr),
       ⟨M, e1⟩ ⊨ n ⇒ (N, e2) -> ⟨M, EDeref e1⟩ ⊨ n ⇒ ⟨N, EDeref e2⟩
    | EStep_deref_O : forall (M:Memory.t) (l:Memory.Loc.t),
	l < length M -> ⟨M, EDeref (ELoc l)⟩ ⊨ 0 ⇒ ⟨M, Memory.get l M⟩
    | EStep_assign_l : forall (n:nat) (M N:Memory.t) (e1 e2 e3:expr), 
       ⟨M, e1⟩ ⊨ n ⇒ (N, e3) -> ⟨M, EAssign e1 e2⟩ ⊨ n ⇒ ⟨N, EAssign e3 e2⟩
    | EStep_assign_r : forall (n:nat) (M N:Memory.t) (v e1 e2:expr),
       svalue n v -> ⟨M, e1⟩ ⊨ n ⇒ (N, e2) -> 
       ⟨M, EAssign v e1⟩ ⊨ n ⇒ ⟨N, EAssign v e2⟩
    | EStep_assign : forall (M:Memory.t) (l:Memory.Loc.t) (e v:expr), 
       l < length M -> svalue 0 v -> 
       ⟨M, EAssign (ELoc l) v⟩ ⊨ 0 ⇒ ⟨Memory.set l v M, v⟩
    | EStep_box : forall (n:nat) (M N:Memory.t) (e1 e2:expr),
       ⟨M, e1⟩ ⊨ S n ⇒ (N, e2) -> ⟨M, EBox e1⟩ ⊨ n ⇒ ⟨N, EBox e2⟩
    | EStep_unbox : forall (n:nat) (M N:Memory.t) (e1 e2:expr),
       ⟨M, e1⟩ ⊨ n ⇒ (N, e2) -> ⟨M, EUnbox e1⟩ ⊨ S n ⇒ ⟨N, EUnbox e2⟩
    | EStep_unbox_O : forall (M:Memory.t) (v:expr),
       svalue 1 v -> ⟨M, EUnbox (EBox v)⟩ ⊨ 1 ⇒ ⟨M, v⟩
    | EStep_run : forall (n:nat) (M N:Memory.t) (e1 e2:expr),
       ⟨M, e1⟩ ⊨ n ⇒ (N, e2) -> ⟨M, ERun e1⟩ ⊨ n ⇒ ⟨N, ERun e2⟩
    | EStep_run_O : forall (M:Memory.t) (v:expr),
       svalue 1 v -> ⟨M, ERun (EBox v)⟩ ⊨ 0 ⇒ ⟨M, v⟩
    | EStep_lift : forall (n:nat) (M N:Memory.t) (e1 e2:expr),
       ⟨M, e1⟩ ⊨ n ⇒ (N, e2) -> ⟨M, ELift e1⟩ ⊨ n ⇒ ⟨N, ELift e2⟩
    | EStep_lift_O : forall (M:Memory.t) (v:expr),
       svalue 0 v -> ⟨M, ELift v⟩ ⊨ 0 ⇒ ⟨M, EBox v⟩
  where "s1 '⊨' n '⇒' s2" := (sstep n s1 s2).

  (** *** Natural Semantics *)
  
  (** ** Depth *)
  Fixpoint depth (e:expr) : nat :=
    match e with
    | EConst _ => 0
    | EVar _ => 0
    | EAbs _ e => depth e
    | EFix _ _ e => depth e
    | EApp e1 e2 => max (depth e1) (depth e2)
    | ELoc _ => 0
    | ERef e => depth e
    | EDeref e => depth e
    | EAssign e1 e2 => max (depth e1) (depth e2)
    | EBox e => pred (depth e)
    | EUnbox e => S (depth e)
    | ERun e => depth e
    | ELift e => depth e
    end.

  Fixpoint memory_depth (M:Memory.t) : nat :=
    match M with
    | nil => 0
    | cons e M => max (depth e) (memory_depth M)
    end.

  (** ** Free Variables *)
  Fixpoint fv (n:nat) (B:BindingSet.t) (e:expr) : VarSet.t :=
    match e with
    | EConst _ => VarSet.empty
    | EVar x => BindingSet.varSet x n B
    | EAbs x e => fv n (BindingSet.add x n B) e
    | EFix f x e => fv n (BindingSet.add f n (BindingSet.add x n B)) e
    | EApp e1 e2 => VarSet.union (fv n B e1) (fv n B e2)
    | ELoc _ => VarSet.empty
    | ERef e => fv n B e
    | EDeref e => fv n B e
    | EAssign e1 e2 => VarSet.union (fv n B e1) (fv n B e2)
    | EBox e => fv (S n) B e
    | EUnbox e => fv (pred n) (BindingSet.remove n B) e
    | ERun e => fv n B e
    | ELift e => fv n B e
    end.

  (** ** Bounded Variables *)
  Fixpoint bv (n:nat) (e:expr) : VarSet.t :=
    match e with
    | EConst _ => VarSet.empty
    | EVar _ => VarSet.empty
    | EAbs x e => VarSet.union (BindingSet.bindSet x n) (bv n e)
    | EFix f x e => VarSet.union (BindingSet.bindSet f n)
        (VarSet.union (BindingSet.bindSet x n) (bv n e))
    | EApp e1 e2 => VarSet.union (bv n e1) (bv n e2)
    | ELoc _ => VarSet.empty
    | ERef e => bv n e
    | EDeref e => bv n e
    | EAssign e1 e2 => VarSet.union (bv n e1) (bv n e2)
    | EBox e => bv (S n) e
    | EUnbox e => bv (pred n) e
    | ERun e => bv n e
    | ELift e => bv n e
    end.

  (** ** Fresh variables *)
  Fixpoint fresh (e:expr) : var :=
    match e with
    | EConst _ => 0
    | EVar x => S x
    | EAbs x e => max (S x) (fresh e)
    | EFix f x e => max (S f) (max (S x) (fresh e))
    | EApp e1 e2 => max (fresh e1) (fresh e2)
    | ELoc _ => 0
    | ERef e => fresh e
    | EDeref e => fresh e
    | EAssign e1 e2 => max (fresh e1) (fresh e2)
    | EBox e => fresh e
    | EUnbox e => fresh e
    | ERun e => fresh e
    | ELift e => fresh e
    end.

End CalculusRaw.

Module Type ReplacementCalculus (Repl:Replacement) <: StagedCalculus.
  Module CRaw := CalculusRaw Repl.

  Include Repl.
  Import CRaw.
  
  Module MemoryType := MemoryType.
  Module Memory := Memory.

  Definition var := var.
  Definition const := const.
  Definition location := location.
  Definition expr := expr.

  Definition svalue := svalue.
  Definition memory_svalue := memory_svalue.
  Definition ssticks := ssticks.

  Definition state := state.

  Definition ssubst := ssubst.
  Definition sstep := sstep.

  Definition depth := depth.
  Definition memory_depth := memory_depth.

  Definition fresh := fresh.

  Definition beq_var := beq_nat.
End ReplacementCalculus.

(** * Calculus *)
Module Calculus (Repl:Replacement) <: ReplacementCalculus Repl.

  Include (ReplacementCalculus Repl).

End Calculus.

(** * Lisp-Like Calculus *)
Module LispLikeReplacement <: Replacement.

  Definition rho := fun n => beq_nat n 0.

  Lemma rho_O :
    rho 0 = true.
  Proof.
    reflexivity.
  Qed.

End LispLikeReplacement.

Module LispLikeCalculus := Calculus LispLikeReplacement.
