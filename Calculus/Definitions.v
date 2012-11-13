Require Import Coq.Relations.Relations.
Require Import "Calculus/Sets".

Open Scope type_scope.

(** * Calculus *)
Module Type Calculus.

  Parameter var : Type.
  Parameter expr : Type.

  Parameter beq_var : var -> var -> bool.

  Declare Module MemoryType : MemoryType.
  Module Memory := Memory MemoryType.
  
  Parameter value : expr -> Prop.
  Parameter sticks : expr -> Prop.

  Definition state : Type := Memory.t * expr.

  Parameter subst : var -> expr -> expr -> expr.
  Parameter step : relation state.

  Notation "'⟨' M ',' e '⟩'" := (M, e) (at level 40).

  Notation "s1 '⇒' s2" := (step s1 s2) (at level 40).
  Notation "s1 '⇒*' s2" :=
    (clos_trans_1n state step s1 s2) (at level 40).
  Notation "s1 '⇒+' s2" :=
    (clos_refl_trans state step s1 s2) (at level 40).
 
End Calculus.

(** * Staged Calculus *)
Module Type StagedCalculus.

  Parameter var : Type.
  Parameter expr : Type.

  Parameter beq_var : var -> var -> bool.

  Module MemoryType <: MemoryType.
    Definition data := expr.
    Parameter default : expr.
  End MemoryType.
  Module Memory := Memory MemoryType.

  Parameter svalue : nat -> expr -> Prop.
  Parameter ssticks : nat -> expr -> Prop.

  Definition state : Type := Memory.t * expr.

  Parameter ssubst : nat -> StageSet.t -> var -> expr -> expr -> expr.
  Parameter sstep : nat -> relation state.

  Notation "'⟨' M ',' e '⟩'" := (M, e) (at level 40).

  Notation "s1 '⊨' n '⇒' s2" := (sstep n s1 s2) (at level 40).
  Notation "s1 '⊨' n '⇒*' s2" :=
    (clos_trans_1n state (sstep n) s1 s2) (at level 40).
  Notation "s1 '⊨' n '⇒+' s2" :=
    (clos_refl_trans state (sstep n) s1 s2) (at level 40).

End StagedCalculus.

(** * Calculus Builder *)
Module MakeCalculus (S:StagedCalculus) <: Calculus <: StagedCalculus.
  
  Include S.

  Definition value := svalue 0.
  Definition sticks := ssticks 0.

  Definition subst := ssubst 0 StageSet.empty.
  Definition step := sstep 0.

End MakeCalculus.
