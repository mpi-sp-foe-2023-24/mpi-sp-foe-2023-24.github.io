Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Hoare1.

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

From PLF Require Import Hoare1.
Import Check.

Goal True.

idtac "-------------------  hoare_asgn_examples_2  --------------------".
idtac " ".

idtac "#> assn_sub_ex1'".
idtac "Possible points: 1".
check_type @assn_sub_ex1' (
({{Hoare.Aexp_of_aexp (AId X) <= Hoare.Aexp_of_nat 5}}
 X := (ANum 2) * (AId X)
 {{Hoare.Aexp_of_aexp (AId X) <= Hoare.Aexp_of_nat 10}})).
idtac "Assumptions:".
Abort.
Print Assumptions assn_sub_ex1'.
Goal True.
idtac " ".

idtac "#> assn_sub_ex2'".
idtac "Possible points: 1".
check_type @assn_sub_ex2' (
({{Hoare.Aexp_of_nat 0 <= Hoare.Aexp_of_nat 3 /\
   Hoare.Aexp_of_nat 3 <= Hoare.Aexp_of_nat 5}} X := (ANum 3)
 {{Hoare.Aexp_of_nat 0 <= Hoare.Aexp_of_aexp (AId X) /\
   Hoare.Aexp_of_aexp (AId X) <= Hoare.Aexp_of_nat 5}})).
idtac "Assumptions:".
Abort.
Print Assumptions assn_sub_ex2'.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_example4  --------------------".
idtac " ".

idtac "#> hoare_asgn_example4".
idtac "Possible points: 2".
check_type @hoare_asgn_example4 (
({{Hoare.assert_of_Prop True}} X := (ANum 1); Y := (ANum 2)
 {{Hoare.Aexp_of_aexp (AId X) = Hoare.Aexp_of_nat 1 /\
   Hoare.Aexp_of_aexp (AId Y) = Hoare.Aexp_of_nat 2}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_example4.
Goal True.
idtac " ".

idtac "-------------------  swap_exercise  --------------------".
idtac " ".

idtac "#> swap_exercise".
idtac "Possible points: 3".
check_type @swap_exercise (
({{Hoare.Aexp_of_aexp (AId X) <= Hoare.Aexp_of_aexp (AId Y)}} swap_program
 {{Hoare.Aexp_of_aexp (AId Y) <= Hoare.Aexp_of_aexp (AId X)}})).
idtac "Assumptions:".
Abort.
Print Assumptions swap_exercise.
Goal True.
idtac " ".

idtac "-------------------  invalid_triple  --------------------".
idtac " ".

idtac "#> invalid_triple".
idtac "Advanced".
idtac "Possible points: 6".
check_type @invalid_triple (
(~
 (forall (a : aexp) (n : nat),
  {{Hoare.Aexp_of_aexp a = Hoare.Aexp_of_nat n}} X := (ANum 3); Y := a
  {{Hoare.Aexp_of_aexp (AId Y) = Hoare.Aexp_of_nat n}}))).
idtac "Assumptions:".
Abort.
Print Assumptions invalid_triple.
Goal True.
idtac " ".

idtac "-------------------  if_minus_plus  --------------------".
idtac " ".

idtac "#> if_minus_plus".
idtac "Possible points: 2".
check_type @if_minus_plus (
({{Hoare.assert_of_Prop True}}
 if (AId X) <= (AId Y) then Z := (AId Y) - (AId X)
 else Y := (AId X) + (AId Z) end
 {{Hoare.Aexp_of_aexp (AId Y) =
   Hoare.Aexp_of_aexp (AId X) + Hoare.Aexp_of_aexp (AId Z)}})).
idtac "Assumptions:".
Abort.
Print Assumptions if_minus_plus.
Goal True.
idtac " ".

idtac "-------------------  if1_ceval  --------------------".
idtac " ".

idtac "#> If1.if1true_test".
idtac "Possible points: 1".
check_type @If1.if1true_test (
(If1.ceval (If1.CIf1 <{ (AId X) = (ANum 0) }> (If1.CAsgn X (ANum 1)))
   empty_st (X !-> 1))).
idtac "Assumptions:".
Abort.
Print Assumptions If1.if1true_test.
Goal True.
idtac " ".

idtac "#> If1.if1false_test".
idtac "Possible points: 1".
check_type @If1.if1false_test (
(If1.ceval (If1.CIf1 <{ (AId X) = (ANum 0) }> (If1.CAsgn X (ANum 1)))
   (X !-> 2) (X !-> 2))).
idtac "Assumptions:".
Abort.
Print Assumptions If1.if1false_test.
Goal True.
idtac " ".

idtac "-------------------  hoare_if1  --------------------".
idtac " ".

idtac "#> Manually graded: If1.hoare_if1".
idtac "Possible points: 2".
print_manual_grade If1.manual_grade_for_hoare_if1.
idtac " ".

idtac "-------------------  hoare_if1_good  --------------------".
idtac " ".

idtac "#> If1.hoare_if1_good".
idtac "Possible points: 2".
check_type @If1.hoare_if1_good (
(If1.hoare_triple
   (Hoare.Aexp_of_aexp (AId X) + Hoare.Aexp_of_aexp (AId Y) =
    Hoare.Aexp_of_aexp (AId Z))
   (If1.CIf1 <{ (AId Y) <> (ANum 0) }> (If1.CAsgn X <{ (AId X) + (AId Y) }>))
   (Hoare.Aexp_of_aexp (AId X) = Hoare.Aexp_of_aexp (AId Z)))).
idtac "Assumptions:".
Abort.
Print Assumptions If1.hoare_if1_good.
Goal True.
idtac " ".

idtac "-------------------  hoare_havoc  --------------------".
idtac " ".

idtac "#> Himp.hoare_havoc".
idtac "Possible points: 3".
check_type @Himp.hoare_havoc (
(forall (Q : Assertion) (X : String.string),
 Himp.hoare_triple (Himp.havoc_pre X Q) (Himp.CHavoc X) Q)).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.hoare_havoc.
Goal True.
idtac " ".

idtac "-------------------  havoc_post  --------------------".
idtac " ".

idtac "#> Himp.havoc_post".
idtac "Possible points: 3".
check_type @Himp.havoc_post (
(forall (P : Assertion) (X : String.string),
 Himp.hoare_triple P (Himp.CHavoc X)
   (fun st : state => exists n : nat, (P [X |-> (ANum n)]) st))).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.havoc_post.
Goal True.
idtac " ".

idtac "-------------------  assert_vs_assume  --------------------".
idtac " ".

idtac "#> HoareAssertAssume.assert_assume_differ".
idtac "Possible points: 1".
check_type @HoareAssertAssume.assert_assume_differ (
(exists (P : Assertion) (b : bexp) (Q : Assertion),
   HoareAssertAssume.hoare_triple P (HoareAssertAssume.CAssume b) Q /\
   ~ HoareAssertAssume.hoare_triple P (HoareAssertAssume.CAssert b) Q)).
idtac "Assumptions:".
Abort.
Print Assumptions HoareAssertAssume.assert_assume_differ.
Goal True.
idtac " ".

idtac "#> HoareAssertAssume.assert_implies_assume".
idtac "Possible points: 1".
check_type @HoareAssertAssume.assert_implies_assume (
(forall (P : Assertion) (b : bexp) (Q : Assertion),
 HoareAssertAssume.hoare_triple P (HoareAssertAssume.CAssert b) Q ->
 HoareAssertAssume.hoare_triple P (HoareAssertAssume.CAssume b) Q)).
idtac "Assumptions:".
Abort.
Print Assumptions HoareAssertAssume.assert_implies_assume.
Goal True.
idtac " ".

idtac "#> HoareAssertAssume.assert_assume_example".
idtac "Possible points: 4".
check_type @HoareAssertAssume.assert_assume_example (
(HoareAssertAssume.hoare_triple (Hoare.assert_of_Prop True)
   (HoareAssertAssume.CSeq
      (HoareAssertAssume.CAssume <{ (AId X) = (ANum 1) }>)
      (HoareAssertAssume.CSeq
         (HoareAssertAssume.CAsgn X <{ (AId X) + (ANum 1) }>)
         (HoareAssertAssume.CAssert <{ (AId X) = (ANum 2) }>)))
   (Hoare.assert_of_Prop True))).
idtac "Assumptions:".
Abort.
Print Assumptions HoareAssertAssume.assert_assume_example.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 27".
idtac "Max points - advanced: 33".
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
idtac "---------- assn_sub_ex1' ---------".
Print Assumptions assn_sub_ex1'.
idtac "---------- assn_sub_ex2' ---------".
Print Assumptions assn_sub_ex2'.
idtac "---------- hoare_asgn_example4 ---------".
Print Assumptions hoare_asgn_example4.
idtac "---------- swap_exercise ---------".
Print Assumptions swap_exercise.
idtac "---------- if_minus_plus ---------".
Print Assumptions if_minus_plus.
idtac "---------- If1.if1true_test ---------".
Print Assumptions If1.if1true_test.
idtac "---------- If1.if1false_test ---------".
Print Assumptions If1.if1false_test.
idtac "---------- hoare_if1 ---------".
idtac "MANUAL".
idtac "---------- If1.hoare_if1_good ---------".
Print Assumptions If1.hoare_if1_good.
idtac "---------- Himp.hoare_havoc ---------".
Print Assumptions Himp.hoare_havoc.
idtac "---------- Himp.havoc_post ---------".
Print Assumptions Himp.havoc_post.
idtac "---------- HoareAssertAssume.assert_assume_differ ---------".
Print Assumptions HoareAssertAssume.assert_assume_differ.
idtac "---------- HoareAssertAssume.assert_implies_assume ---------".
Print Assumptions HoareAssertAssume.assert_implies_assume.
idtac "---------- HoareAssertAssume.assert_assume_example ---------".
Print Assumptions HoareAssertAssume.assert_assume_example.
idtac "".
idtac "********** Advanced **********".
idtac "---------- invalid_triple ---------".
Print Assumptions invalid_triple.
Abort.

(* 2023-11-01 16:32 *)
