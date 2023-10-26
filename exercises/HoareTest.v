Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Hoare.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From PLF Require Import Hoare.
Import Check.

Goal True.

idtac "-------------------  hoare_post_true  --------------------".
idtac " ".

idtac "#> hoare_post_true".
idtac "Possible points: 1".
check_type @hoare_post_true (
(forall (P Q : Assertion) (c : com),
 (forall st : state, Q st) -> {{P}} c {{Q}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_post_true.
Goal True.
idtac " ".

idtac "-------------------  hoare_pre_false  --------------------".
idtac " ".

idtac "#> hoare_pre_false".
idtac "Possible points: 1".
check_type @hoare_pre_false (
(forall (P Q : Assertion) (c : com),
 (forall st : state, ~ P st) -> {{P}} c {{Q}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_pre_false.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_wrong  --------------------".
idtac " ".

idtac "#> Manually graded: hoare_asgn_wrong".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_hoare_asgn_wrong.
idtac " ".

idtac "-------------------  hoare_asgn_fwd  --------------------".
idtac " ".

idtac "#> hoare_asgn_fwd".
idtac "Advanced".
idtac "Possible points: 3".
check_type @hoare_asgn_fwd (
(forall (m : nat) (a : aexp) (P : state -> Prop),
 {{fun st : state => P st /\ st X = m}} X := a
 {{fun st : state =>
   P (@Maps.t_update nat st X m) /\
   st X = aeval (@Maps.t_update nat st X m) a}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_fwd.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 4".
idtac "Max points - advanced: 7".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "CSeq_congruence".
idtac "fold_constants_bexp_sound".
idtac "succ_hastype_nat__hastype_nat".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- hoare_post_true ---------".
Print Assumptions hoare_post_true.
idtac "---------- hoare_pre_false ---------".
Print Assumptions hoare_pre_false.
idtac "---------- hoare_asgn_wrong ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
idtac "---------- hoare_asgn_fwd ---------".
Print Assumptions hoare_asgn_fwd.
Abort.

(* 2023-10-26 16:16 *)
