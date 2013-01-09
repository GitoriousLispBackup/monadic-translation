Require Import Coq.Arith.Arith.
Require Export "Misc/LibTactics".

(* http://web.cecs.pdx.edu/~apt/cs510coq/new_stlc.v *)
Ltac case_beq_nat x y :=
  let E := fresh "E" in 
  case_eq (beq_nat x y); intro E; 
     [(try (rewrite E in *|-); apply (beq_nat_true x y) in E; subst x) 
     | (try (rewrite E in *|-); apply beq_nat_false in E)] .


Tactic Notation "cases" constr(E) "as" ident(v) "eqn:" ident(H) := 
  let X := fresh v in 
  set (X := E) in *; def_to_eq X H E;
  destruct X.


Tactic Notation "rewrite_eq" constr(E1) constr(E2) :=
  let X := fresh "H" in
  let Eqn := fresh "H" in
  set (X := E1) in *; 
  assert(X=E2) as Eqn ; [subst ; reflexivity| rewrite Eqn in *|-* ; clear Eqn X].
