Require Import "Calculus/Definitions".
Require Import Coq.Logic.Classical.

(** * Definitions *)

(** ** Terminology *)
Module Terminology (C:Calculus).

  Import C.

  Definition blocks (e:expr) : Prop :=
    value e \/ sticks e.

  Definition halts_at (s1 s2:state) : Prop := 
    s1 ⇒* s2 /\ let (_, e2) := s2 in blocks e2.

  Definition halts (s1:state) : Prop :=
    exists s2:state, halts_at s1 s2.

  Definition not_halts (s1:state) : Prop :=
    forall (s2:state), ~ halts_at s1 s2.

  Definition progresses (s1:state) : Prop :=
    exists s2:state, s1 ⇒ s2.

  Definition not_progresses (s1:state) : Prop :=
    forall s2:state, ~ s1 ⇒ s2.

  Definition always (P:state -> Prop) (s1:state) : Prop :=
    forall s2:state, s1 ⇒* s2  -> P s2.

  Definition eventually (P:state -> Prop) (s1:state) : Prop :=
    exists s2:state, s1 ⇒* s2  /\ P s2.

End Terminology.

(** ** Staged Terminology *)
Module StagedTerminology (C:StagedCalculus).

  Import C.

  Definition sblocks (n:nat) (e:expr) : Prop :=
    svalue n e \/ ssticks n e.

  Definition shalts_at (n:nat) (s1 s2:state) : Prop := 
    s1 ⊨ n ⇒ s2 /\ let (_, e2) := s2 in sblocks n e2.

  Definition shalts (n:nat) (s1:state) : Prop :=
    exists s2:state, shalts_at n s1 s2.

  Definition not_shalts (n:nat) (s1:state) : Prop :=
    forall (s2:state), ~ shalts_at n s1 s2.

  Definition sprogresses (n:nat) (s1:state) : Prop :=
    exists s2:state, s1 ⊨ n ⇒ s2.

  Definition not_sprogresses (n:nat) (s1:state) : Prop :=
    forall s2:state, ~ s1 ⊨ n ⇒ s2.

  Definition salways (n:nat) (P:state -> Prop) (s1:state) : Prop :=
    forall s2:state, s1 ⊨ n ⇒* s2  -> P s2.

  Definition seventually (n:nat) (P:state -> Prop) (s1:state) : Prop :=
    exists s2:state, s1 ⊨ n ⇒* s2  /\ P s2.

End StagedTerminology.

(** * Properties *)

(** ** Terminology Properties *)
Module TerminologyProperties (C:Calculus).

  Module Terminology := Terminology C.
  Import Terminology.
  Import C.

  Lemma halts_not_halts:
    forall s:state,
    halts s -> ~ not_halts s.
  Proof.
    intros ; red ; intros.
    apply all_not_not_ex in H0.
    contradiction.
  Qed.

  Lemma not_halts_halts:
    forall s:state,
    not_halts s -> ~ halts s.
  Proof.
    intros.
    apply all_not_not_ex in H.
    assumption.
  Qed.

  Lemma progresses_not_progresses:
    forall s:state,
    progresses s -> ~ not_progresses s.
  Proof.
    intros ; red ; intros.
    apply all_not_not_ex in H0.
    contradiction.
  Qed.

  Lemma not_progresses_progresses:
    forall s:state,
    not_progresses s -> ~ progresses s.
  Proof.
    intros.
    apply all_not_not_ex in H.
    assumption.
  Qed.

  Lemma eventually_not_always:
    forall (P:state -> Prop) (s:state),
    eventually P s -> ~ always (fun s => ~ P s) s.
  Proof.
    intros ; red ; intros.
    destruct H ; destruct H.
    specialize (H0 x H) ; contradiction.
  Qed.

  Lemma always_not_eventually:
    forall (P:state -> Prop) (s:state),
    always P s -> ~ eventually (fun s => ~ P s) s.
  Proof.
    intros ; red ; intros.
    destruct H0 ; destruct H0.
    specialize (H x H0) ; contradiction.
  Qed.

End TerminologyProperties.

(** ** Staged Terminology Properties *)

Module StagedTerminologyProperties (C:StagedCalculus).

  Module Terminology := StagedTerminology C.
  Import Terminology.
  Import C.

  Lemma shalts_not_shalts:
    forall (n:nat) (s:state),
    shalts n s -> ~ not_shalts n s.
  Proof.
    intros ; red ; intros.
    apply all_not_not_ex in H0.
    contradiction.
  Qed.

  Lemma not_shalts_shalts:
    forall (n:nat) (s:state),
    not_shalts n s -> ~ shalts n s.
  Proof.
    intros.
    apply all_not_not_ex in H.
    assumption.
  Qed.

  Lemma sprogresses_not_sprogresses:
    forall (n:nat) (s:state),
    sprogresses n s -> ~ not_sprogresses n s.
  Proof.
    intros ; red ; intros.
    apply all_not_not_ex in H0.
    contradiction.
  Qed.

  Lemma not_sprogresses_sprogresses:
    forall (n:nat) (s:state),
    not_sprogresses n s -> ~ sprogresses n s.
  Proof.
    intros.
    apply all_not_not_ex in H.
    assumption.
  Qed.

  Lemma seventually_not_salways:
    forall (P:state -> Prop) (n:nat) (s:state),
    seventually n P s -> ~ salways n (fun s => ~ P s) s.
  Proof.
    intros ; red ; intros.
    destruct H ; destruct H.
    specialize (H0 x H) ; contradiction.
  Qed.

  Lemma salways_not_seventually:
    forall (P:state -> Prop) (n:nat) (s:state),
    salways n P s -> ~ seventually n (fun s => ~ P s) s.
  Proof.
    intros ; red ; intros.
    destruct H0 ; destruct H0.
    specialize (H x H0) ; contradiction.
  Qed.

End StagedTerminologyProperties.
