Require Import Permutation List Lia.

Inductive value := x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7.
Inductive variable := aux | num: value -> variable.
Definition variable_eq_dec (x y: variable): {x=y} + {x<>y}.
Proof.
  destruct x, y.
  + left; auto.
  + right; abstract congruence.
  + right; abstract congruence.
  + destruct v, v0; try (left; abstract congruence); (right; abstract congruence).
Defined.

Inductive assignment := assign: variable -> variable -> assignment.
Inductive comparison := GT: forall (more less: value), comparison.

Inductive step :=
| assignments: forall (L: list assignment), step
| conditional: forall (c: comparison) (positive negative: step), step.

Definition algorithm := list step.

Definition instantation := variable -> nat.

Definition is_increasing (i: instantation) :=
  i (num x0) <= i (num x1) /\
  i (num x1) <= i (num x2) /\
  i (num x2) <= i (num x3) /\
  i (num x3) <= i (num x4) /\
  i (num x4) <= i (num x5) /\
  i (num x5) <= i (num x6) /\
  i (num x6) <= i (num x7).
Definition list_of_values (i: instantation) :=
  i (num x0) :: i (num x1) :: i (num x2) :: i (num x3) :: i (num x4) :: i (num x5) :: i (num x6) :: i (num x7) :: nil.
Definition is_permutation (i1 i2: instantation) := Permutation (list_of_values i1) (list_of_values i2).

Definition is_sorted (start result: instantation) := is_increasing result /\ is_permutation start result.

Definition run_assignment (values: instantation) (a: assignment): instantation.
Proof.
  destruct a as [v1 v2].
  exact (fun i => if variable_eq_dec i v1 then values v2 else values i).
Defined.

Definition run_step (values: instantation) (s: step): instantation.
Proof.
  induction s.
  + induction L.
    - exact values.
    - exact (run_assignment IHL a).
  + destruct c.
    exact (if Compare_dec.gt_dec (values (num more)) (values (num less)) then IHs1 else IHs2).
Defined.

Definition run_algorithm (values: instantation) (algo: algorithm): instantation.
Proof.
  induction algo.
  + exact values.
  + exact (run_step IHalgo a).
Defined.

Definition run_algorithm_tail (values: instantation) (s: step) (algo: algorithm):
  run_algorithm values (algo ++ s :: nil) = run_algorithm (run_step values s) algo.
Proof.
  induction algo.
  + simpl. auto.
  + simpl. rewrite IHalgo. auto.
Qed.

Definition count_comparisons_in_step (s: step): nat.
Proof.
  induction s.
  + exact 0.
  + exact (1 + PeanoNat.Nat.max IHs1 IHs2).
Defined.
Definition count_comparisons_in_algorithm (a: algorithm): nat.
Proof.
  induction a as [| s L].
  + exact 0.
  + exact (IHL + count_comparisons_in_step s).
Defined.

Definition do_nothing := assignments nil.
Definition swap (x y: value) :=
  assign (num y) aux ::
  assign (num x) (num y) ::
  assign aux (num x) ::
  nil.

Definition property (L: list comparison) (i: instantation): Prop.
Proof.
  induction L.
  + exact True.
  + destruct a. exact (IHL /\ i (num less) <= i (num more)).
Defined.

Definition step1 := conditional (GT x0 x1) (assignments (swap x0 x1)) do_nothing.
Definition prop1 := GT x1 x0 :: nil.
Definition step2 := conditional (GT x2 x3) (assignments (swap x2 x3)) do_nothing.
Definition prop2 := GT x3 x2 :: prop1.
Definition step3 := conditional (GT x4 x5) (assignments (swap x4 x5)) do_nothing.
Definition prop3 := GT x5 x4 :: prop2.
Definition step4 := conditional (GT x6 x7) (assignments (swap x6 x7)) do_nothing.
Definition prop4 := GT x7 x6 :: prop3.
Definition step5 := conditional (GT x1 x3) (assignments (swap x1 x3 ++ swap x0 x2)) do_nothing.
Definition prop5 := GT x3 x1 :: prop4.
Definition step6 := conditional (GT x5 x7) (assignments (swap x5 x7 ++ swap x4 x6)) do_nothing.
Definition prop6 := GT x7 x5 :: prop5.
Definition step7 := conditional (GT x3 x7) (assignments (swap x0 x4 ++ swap x1 x5 ++ swap x2 x6 ++ swap x3 x7)) do_nothing.
Definition prop7 := GT x7 x3 :: prop6.
Definition step8_9 := conditional (GT x5 x3)
                       do_nothing
                       (conditional (GT x5 x1)
                        (assignments (swap x3 x5 ++ swap x2 x4))
                        (assignments ( 
                         assign (num x2) aux :: assign (num x4) (num x2) :: assign (num x0) (num x4) :: assign aux (num x0) ::
                         assign (num x3) aux :: assign (num x5) (num x3) :: assign (num x1) (num x5) :: assign aux (num x1) :: nil))).
Definition prop9 := GT x5 x3 :: prop6.
Definition step10_11 := conditional (GT x1 x4)
                         (conditional (GT x0 x4)
                          (assignments (assign (num x1) aux :: assign (num x2) (num x1) :: assign (num x3) (num x2) ::
                                        assign (num x4) (num x3) :: assign (num x0) (num x4) :: assign aux (num x0) :: nil))
                          (assignments (assign (num x2) aux :: assign (num x3) (num x2) :: assign (num x4) (num x3) ::
                                        assign (num x1) (num x4) :: assign aux (num x1) :: nil)))
                         (conditional (GT x3 x4)
                          (assignments (assign (num x3) aux :: assign (num x4) (num x3) :: assign (num x2) (num x4) ::
                                        assign aux (num x2) :: nil))
                          (assignments (swap x2 x3))).
Definition prop11 := GT x1 x0 :: GT x2 x1 :: GT x4 x2 :: GT x4 x3 :: GT x5 x4 :: GT x7 x5 :: GT x7 x6 :: nil.
Definition step12_13 := conditional (GT x1 x3)
                         (conditional (GT x0 x3)
                          (assignments (assign (num x1) aux :: assign (num x2) (num x1) :: assign (num x3) (num x2) ::
                                        assign (num x0) (num x3) :: assign aux (num x0) :: nil))
                          (assignments (assign (num x2) aux :: assign (num x3) (num x2) :: assign (num x1) (num x3) ::
                                        assign aux (num x1) :: nil)))
                         (conditional (GT x2 x3)
                          (assignments (swap x2 x3)) do_nothing).
Definition prop13 := GT x1 x0 :: GT x2 x1 :: GT x3 x2 :: GT x4 x3 :: GT x5 x4 :: GT x7 x5 :: GT x7 x6 :: nil.
Definition step14_15_16 :=
  conditional (GT x3 x6)
   (conditional (GT x1 x6)
     (conditional (GT x0 x6)
      (assignments (assign (num x1) aux :: assign (num x2) (num x1) :: assign (num x3) (num x2) :: assign (num x4) (num x3) ::
                    assign (num x5) (num x4) :: assign (num x6) (num x5) :: assign (num x0) (num x6) :: assign aux (num x0) :: nil))
      (assignments (assign (num x2) aux :: assign (num x3) (num x2) :: assign (num x4) (num x3) :: assign (num x5) (num x4) ::
                    assign (num x6) (num x5) :: assign (num x1) (num x6) :: assign aux (num x1) :: nil)))
     (conditional (GT x2 x6)
      (assignments (assign (num x3) aux :: assign (num x4) (num x3) :: assign (num x5) (num x4) :: assign (num x6) (num x5) ::
                    assign (num x2) (num x6) :: assign aux (num x2) :: nil))
      (assignments (assign (num x4) aux :: assign (num x5) (num x4) :: assign (num x6) (num x5) :: assign (num x3) (num x6) ::
                    assign aux (num x3) :: nil))))
   (conditional (GT x5 x6)
     (conditional (GT x4 x6)
      (assignments (assign (num x5) aux :: assign (num x6) (num x5) :: assign (num x4) (num x6) :: assign aux (num x4) :: nil))
      (assignments (swap x5 x6)))
     do_nothing).
Definition prop16 := GT x1 x0 :: GT x2 x1 :: GT x3 x2 :: GT x4 x3 :: GT x5 x4 :: GT x6 x5 :: GT x7 x6 :: nil.

Definition sort8: algorithm := step14_15_16 :: step12_13 :: step10_11 :: step8_9 :: step7 ::
                               step6 :: step5 :: step4 :: step3 :: step2 :: step1 :: nil.

Eval compute in count_comparisons_in_algorithm sort8.

Ltac T1 after := intros; repeat split; simpl in *; unfold after; clear after;
     repeat destruct Compare_dec.gt_dec; repeat (destruct variable_eq_dec; try congruence); lia.

Definition step1_condition (before: instantation):
  let after := run_algorithm before (step1 :: nil) in
  property prop1 after.
Proof.
  T1 after.
Qed.
Definition step2_after_step1_condition (before: instantation)
  (H: property prop1 before):
  let after := run_algorithm before (step2 :: nil) in
  property prop2 after.
Proof.
  T1 after.
Qed.
Definition step3_after_step2_condition (before: instantation)
  (H: property prop2 before):
  let after := run_algorithm before (step3 :: nil) in
  property prop3 after.
Proof.
  T1 after.
Qed.
Definition step4_after_step3_condition (before: instantation)
  (H: property prop3 before):
  let after := run_algorithm before (step4 :: nil) in
  property prop4 after.
Proof.
  T1 after.
Qed.
Definition step5_after_step4_condition (before: instantation)
  (H: property prop4 before):
  let after := run_algorithm before (step5 :: nil) in
  property prop5 after.
Proof.
  T1 after.
Qed.
Definition step6_after_step5_condition (before: instantation)
  (H: property prop5 before):
  let after := run_algorithm before (step6 :: nil) in
  property prop6 after.
Proof.
  T1 after.
Qed.
Definition step7_after_step6_condition (before: instantation)
  (H: property prop6 before):
  let after := run_algorithm before (step7 :: nil) in
  property prop7 after.
Proof.
  T1 after.
Qed.
Definition step9_after_step7_condition (before: instantation)
  (H: property prop7 before):
  let after := run_algorithm before (step8_9 :: nil) in
  property prop9 after.
Proof.
  T1 after.
Qed.
Definition step11_after_step9_condition (before: instantation)
  (H: property prop9 before):
  let after := run_algorithm before (step10_11 :: nil) in
  property prop11 after.
Proof.
  T1 after.
Qed.
Definition step13_after_step11_condition (before: instantation)
  (H: property prop11 before):
  let after := run_algorithm before (step12_13 :: nil) in
  property prop13 after.
Proof.
  T1 after.
Qed.
Definition step16_after_step13_condition (before: instantation)
  (H: property prop13 before):
  let after := run_algorithm before (step14_15_16 :: nil) in
  property prop16 after.
Proof.
  T1 after.
Qed.


Lemma Permutation_Add_cons A :
  forall (a : A) l1 l2 l2', Add a l2 l2' -> Permutation l1 l2 -> Permutation (a :: l1) l2'.
Proof.
  intros a l1 l2 l2' Hadd HP.
  now etransitivity; [ apply Permutation_cons | apply Permutation_Add, Hadd ].
Qed.

Ltac permutation_solve :=
  intros; now repeat (eapply Permutation_Add_cons; [ repeat econstructor | ]).

Ltac T2 after list_of_values := intros; unfold after, list_of_values; simpl; repeat destruct Compare_dec.gt_dec;
                                repeat (destruct variable_eq_dec; try congruence); permutation_solve.

Definition step1_permutation (before: instantation):
  let after := run_algorithm before (step1 :: nil) in
  Permutation (list_of_values before) (list_of_values after).
Proof.
  T2 after list_of_values.
Qed.
Definition step2_permutation (before: instantation):
  let after := run_algorithm before (step2 :: nil) in
  Permutation (list_of_values before) (list_of_values after).
Proof.
  T2 after list_of_values.
Qed.
Definition step3_permutation (before: instantation):
  let after := run_algorithm before (step3 :: nil) in
  Permutation (list_of_values before) (list_of_values after).
Proof.
  T2 after list_of_values.
Qed.
Definition step4_permutation (before: instantation):
  let after := run_algorithm before (step4 :: nil) in
  Permutation (list_of_values before) (list_of_values after).
Proof.
  T2 after list_of_values.
Qed.
Definition step5_permutation (before: instantation):
  let after := run_algorithm before (step5 :: nil) in
  Permutation (list_of_values before) (list_of_values after).
Proof.
  T2 after list_of_values.
Qed.
Definition step6_permutation (before: instantation):
  let after := run_algorithm before (step6 :: nil) in
  Permutation (list_of_values before) (list_of_values after).
Proof.
  T2 after list_of_values.
Qed.
Definition step7_permutation (before: instantation):
  let after := run_algorithm before (step7 :: nil) in
  Permutation (list_of_values before) (list_of_values after).
Proof.
  T2 after list_of_values.
Qed.
Definition step9_permutation (before: instantation):
  let after := run_algorithm before (step8_9 :: nil) in
  Permutation (list_of_values before) (list_of_values after).
Proof.
  T2 after list_of_values.
Qed.
Definition step11_permutation (before: instantation):
  let after := run_algorithm before (step10_11 :: nil) in
  Permutation (list_of_values before) (list_of_values after).
Proof.
  T2 after list_of_values.
Qed.
Definition step13_permutation (before: instantation):
  let after := run_algorithm before (step12_13 :: nil) in
  Permutation (list_of_values before) (list_of_values after).
Proof.
  T2 after list_of_values.
Qed.
Definition step16_permutation (before: instantation):
  let after := run_algorithm before (step14_15_16 :: nil) in
  Permutation (list_of_values before) (list_of_values after).
Proof.
  T2 after list_of_values.
Qed.

Theorem algorithm_cons (s: step) (a: algorithm) (before: instantation):
  run_algorithm before (s :: a) = run_algorithm (run_algorithm before a) (s :: nil).
Proof.
  simpl. reflexivity.
Qed.

Theorem algorithm_permutation (before: instantation):
  let after := run_algorithm before sort8 in
  Permutation (list_of_values before) (list_of_values after).
Proof.
  unfold sort8.
  assert (Permutation
    (list_of_values (run_algorithm before (step12_13 :: step10_11 :: step8_9 :: step7 :: step6 :: step5 :: step4 :: step3 :: step2 :: step1 :: nil)))
    (list_of_values (run_algorithm before (step14_15_16 :: step12_13 :: step10_11 :: step8_9 :: step7 :: step6 :: step5 :: step4 :: step3 :: step2 :: step1 :: nil)))).
  { rewrite (algorithm_cons step14_15_16). apply step16_permutation. }
  assert (Permutation
    (list_of_values (run_algorithm before (step10_11 :: step8_9 :: step7 :: step6 :: step5 :: step4 :: step3 :: step2 :: step1 :: nil)))
    (list_of_values (run_algorithm before (step12_13 :: step10_11 :: step8_9 :: step7 :: step6 :: step5 :: step4 :: step3 :: step2 :: step1 :: nil)))).
  { rewrite (algorithm_cons step12_13). apply step13_permutation. }
  assert (Permutation
    (list_of_values (run_algorithm before (step8_9 :: step7 :: step6 :: step5 :: step4 :: step3 :: step2 :: step1 :: nil)))
    (list_of_values (run_algorithm before (step10_11 :: step8_9 :: step7 :: step6 :: step5 :: step4 :: step3 :: step2 :: step1 :: nil)))).
  { rewrite (algorithm_cons step10_11). apply step11_permutation. }
  assert (Permutation
    (list_of_values (run_algorithm before (step7 :: step6 :: step5 :: step4 :: step3 :: step2 :: step1 :: nil)))
    (list_of_values (run_algorithm before (step8_9 :: step7 :: step6 :: step5 :: step4 :: step3 :: step2 :: step1 :: nil)))).
  { rewrite (algorithm_cons step8_9). apply step9_permutation. }
  assert (Permutation
    (list_of_values (run_algorithm before (step6 :: step5 :: step4 :: step3 :: step2 :: step1 :: nil)))
    (list_of_values (run_algorithm before (step7 :: step6 :: step5 :: step4 :: step3 :: step2 :: step1 :: nil)))).
  { rewrite (algorithm_cons step7). apply step7_permutation. }
  assert (Permutation
    (list_of_values (run_algorithm before (step5 :: step4 :: step3 :: step2 :: step1 :: nil)))
    (list_of_values (run_algorithm before (step6 :: step5 :: step4 :: step3 :: step2 :: step1 :: nil)))).
  { rewrite (algorithm_cons step6). apply step6_permutation. }
  assert (Permutation
    (list_of_values (run_algorithm before (step4 :: step3 :: step2 :: step1 :: nil)))
    (list_of_values (run_algorithm before (step5 :: step4 :: step3 :: step2 :: step1 :: nil)))).
  { rewrite (algorithm_cons step5). apply step5_permutation. }
  assert (Permutation
    (list_of_values (run_algorithm before (step3 :: step2 :: step1 :: nil)))
    (list_of_values (run_algorithm before (step4 :: step3 :: step2 :: step1 :: nil)))).
  { rewrite (algorithm_cons step4). apply step4_permutation. }
  assert (Permutation
    (list_of_values (run_algorithm before (step2 :: step1 :: nil)))
    (list_of_values (run_algorithm before (step3 :: step2 :: step1 :: nil)))).
  { rewrite (algorithm_cons step3). apply step3_permutation. }
  assert (Permutation
    (list_of_values (run_algorithm before (step1 :: nil)))
    (list_of_values (run_algorithm before (step2 :: step1 :: nil)))).
  { rewrite (algorithm_cons step2). apply step2_permutation. }
  assert (Permutation
    (list_of_values before)
    (list_of_values (run_algorithm before (step1 :: nil)))).
  { apply step1_permutation. }
  repeat (eapply perm_trans; eauto).
Qed.


Definition equivalent (i1 i2: instantation) :=
  forall x y, i1 x <= i1 y <-> i2 x <= i2 y.

Fixpoint distinct (L: list instantation) :=
  match L with
  | x :: (y :: t) as t0 => ~ equivalent x y /\ distinct t0
  | _ => True
  end.

Fixpoint factorial n :=
  match n with
  | O => 1
  | S m => S m * factorial m
  end.

Theorem run_algorithm_nil (i: instantation) : forall x, run_algorithm i nil x = i x.
Proof.
  intros. simpl. auto.
Qed.

Theorem run_step_cons (i: instantation) (a: assignment) (L: list assignment):
  run_step i (assignments (a :: L)) = run_assignment (run_step i (assignments L)) a.
Proof.
  simpl. auto.
Qed.

Theorem equivalent_after_assignment (i1 i2: instantation) (H: equivalent i1 i2) (a: assignment):
  equivalent (run_assignment i1 a) (run_assignment i2 a).
Proof.
  unfold equivalent in *. intros. destruct a.
  destruct v, v0; simpl; repeat (destruct variable_eq_dec); apply H.
Qed.

Theorem equivalent_after_step (i1 i2: instantation) (H: equivalent i1 i2) (s: step):
  equivalent (run_step i1 s) (run_step i2 s).
Proof.
  induction s.
  + induction L.
    - simpl. auto.
    - intros. repeat rewrite run_step_cons. apply equivalent_after_assignment; auto.
  + intros. simpl. destruct c. unfold equivalent in *. intros. repeat (destruct Compare_dec.gt_dec); eauto.
    - pose (H (num more) (num less)). lia.
    - pose (H (num more) (num less)). lia.
Qed.

Theorem equivalent_after_algorithm (i1 i2: instantation) (H: equivalent i1 i2) (a: algorithm):
  equivalent (run_algorithm i1 a) (run_algorithm i2 a).
Proof.
  unfold equivalent in *.
  + induction a; intros; simpl in *.
    - apply H.
    - apply equivalent_after_step; eauto.
Qed.


(* ?? Something about distinct instantations being factorial 8 ?? *)
Theorem max_number_of_distinct_instantations (L: list instantation):
  distinct L -> length L <= factorial 8.
Proof.
Admitted.




(* Extraction to graphviz as flowchart *)
Require Import String.
Open Scope string.

Definition value_to_string (n: value): string :=
  match n with
  | x0 => "x0"
  | x1 => "x1"
  | x2 => "x2"
  | x3 => "x3"
  | x4 => "x4"
  | x5 => "x5"
  | x6 => "x6"
  | x7 => "x7"
  end.
Definition variable_to_string (v: variable): string :=
  match v with
  | aux => "t"
  | num x => value_to_string x
  end.
Definition comparison_to_string (c: comparison) :=
  match c with
  | GT x y => "[label=""" ++ value_to_string x ++ " > " ++ value_to_string y ++ """, shape=""diamond""]; " end.
Definition assignment_to_string (a: assignment) :=
  match a with assign x y => variable_to_string x ++ "=" ++ variable_to_string y end.
Fixpoint assignment_list_to_string_aux (L: list assignment): string :=
  match L with
  | nil => ""
  | x :: nil => assignment_to_string x
  | x :: t => assignment_to_string x ++ "; " ++ assignment_list_to_string_aux t
  end.
Definition assignment_list_to_string L := "[label=""" ++ assignment_list_to_string_aux (rev L) ++ """];".

Eval compute in assignment_list_to_string (swap x0 x1).
Eval compute in comparison_to_string (GT x0 x1).

Definition count_assignment_blocks_in_step (s: step): nat.
Proof.
  induction s.
  + exact 1.
  + exact (IHs1 + IHs2).
Defined.
Eval compute in count_assignment_blocks_in_step step14_15_16.

Definition count_comparison_blocks_in_step (s: step): nat.
Proof.
  induction s.
  + exact 0.
  + exact (1 + IHs1 + IHs2).
Defined.
Eval compute in count_comparison_blocks_in_step step14_15_16.

(* http://poleiro.info/posts/2013-03-31-reading-and-writing-numbers-in-coq.html *)
Definition natToDigit (n : nat) :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
  end.
Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := (natToDigit (Nat.modulo n 10)) ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match Nat.div n 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.
Definition writeNat (n : nat) : string :=
  writeNatAux n n "".
