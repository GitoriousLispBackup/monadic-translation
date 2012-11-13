
Require Import "Calculus/Definitions".

(** * Monad *)
Module Type Monad (S T:Calculus).

End Monad.

(** * Staged Monad *)
Module Type StagedMonad (S T:StagedCalculus).

End StagedMonad.

(** * Translation *)
Module Type Translation (S T:Calculus).

  Parameter trans_expr : S.expr -> T.expr.

  Parameter trans_mem : S.Memory.t -> T.Memory.t.

  Parameter valid :
    forall (e1 e2:S.expr) (M1 M2:S.Memory.t),
    S.step (M1, e1) (M2, e2) -> 
    T.step (trans_mem M1, trans_expr e1) (trans_mem M2, trans_expr e2).

End Translation.

(** * Staged Translation *)
Module Type StagedTranslation (S T:StagedCalculus).

  Parameter trans_expr : S.expr -> T.expr.

  Parameter trans_mem : S.Memory.t -> T.Memory.t.

  Parameter valid :
    forall (e1 e2:S.expr) (M1 M2:S.Memory.t),
    S.sstep 0 (M1, e1) (M2, e2) -> 
    T.sstep 0 (trans_mem M1, trans_expr e1) (trans_mem M2, trans_expr e2).

End StagedTranslation.
