Require Import Coq.omega.Omega.

Module Splitter.

  Record t : Type := mkT {
    get : nat -> nat ;
    injective: forall (m n:nat),
      m <> n -> get m <> get n
  }.

  Lemma id_injective:
    forall (m n:nat),
    m <> n -> m <> n.
  Proof.
    tauto.
  Qed.

  Lemma left_injective:
    forall (acc:t) (m n:nat),
    m <> n -> (fun n => (get acc) (2*n)) m <> (fun n => (get acc) (2*n)) n.
  Proof.
    intros.
    simpl.
    apply (injective acc).
    omega.
  Qed.

  Lemma right_injective:
    forall (acc:t) (m n:nat),
    m <> n -> (fun n => (get acc) (2*n+1)) m <> (fun n => (get acc) (2*n+1)) n.
  Proof.
    intros.
    simpl.
    apply (injective acc).
    omega.
  Qed.

  Definition empty : t := mkT (fun n => n) id_injective.

  Definition left (acc:t) : t := mkT 
    (fun n => (get acc) (2*n)) (left_injective acc).

  Definition right (acc:t) : t := mkT
    (fun n => (get acc) (2*n+1)) (right_injective acc).

  Definition split (acc:t) : t * t := (left acc, right acc).

End Splitter.
