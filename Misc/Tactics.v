Require Import Coq.Arith.Arith.

(* http://web.cecs.pdx.edu/~apt/cs510coq/new_stlc.v *)
Ltac case_beq_nat x y :=
  let E := fresh "E" in 
  case_eq (beq_nat x y); intro E; 
     [(try (rewrite E in *|-); apply (beq_nat_true x y) in E; subst x) 
     | (try (rewrite E in *|-); apply beq_nat_false in E)] .