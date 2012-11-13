Require Import Coq.Relations.Relation_Definitions.

Definition partial_function {X: Type} (R: relation X) : Prop :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Definition function {X: Type} (R: relation X) : Prop :=
  partial_function R /\ 
  forall x : X, exists y : X, R x y.
