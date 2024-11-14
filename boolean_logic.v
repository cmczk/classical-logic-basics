(* Boolean type *)
Inductive bool : Set := true | false.


(* Logical not *)
(*
  t | f
  f | t
*)
Definition not a :=
  match a with
  | true => false
  | false => true
  end.

Check not.
Compute not true. (* = false *)
Compute not false. (* = true *)


(* Logical and *)
(*
  t t | t
  t f | f
  f t | f
  f f | f
*)
Definition and a b :=
  match a with
  | true => b
  | false => false
  end.

Check and.
Compute and true true. (* = true *)
Compute and true false. (* = false *)
Compute and false true. (* = false *)
Compute and false false. (* = false *)


(* Logical or *)
(*
  t t | t
  t f | t
  f t | t
  f f | f
*)
Definition or a b :=
  match a with
  | true => true
  | false => b
  end.

Check or.
Compute or true true. (* = true *)
Compute or true false. (* = true *)
Compute or false true. (* = true *)
Compute or false false. (* = false *)


(* Strong or *)
(*
  t t | f
  t f | t
  f t | t
  f f | f
*)
Definition xor a b :=
  match a with
  | true => not b
  | false => b
  end.

Check xor.
Compute xor true true. (* = false *)
Compute xor true false. (* = true *)
Compute xor false true. (* = true *)
Compute xor false false. (* = false *)


(* Logical implication *)
(*
  t t | t
  t f | f
  f t | t
  f f | t
*)
Definition implication a b :=
  match a with
  | true => b
  | false => true
  end.

Check implication.
Compute implication true true. (* = true *)
Compute implication true false. (* = false *)
Compute implication false true. (* = true *)
Compute implication false false. (* = true *)


(* Logical equivalence *)
(*
  t t | t
  t f | f
  f t | f
  f f | t
*)
Definition equivalence a b :=
  match a with
  | true => b
  | false => not b
  end.

Check equivalence.
Compute equivalence true true. (* = true *)
Compute equivalence true false. (* = false *)
Compute equivalence false true. (* = false *)
Compute equivalence false false. (* = true *)


(* Identity *)
Theorem identity : forall A, implication A A = true.
Proof.
  intros A.
  destruct A.
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
Qed.


(* Double negation *)
Theorem double_negation : forall A : bool, not (not A) = A.
Proof.
  intros A.
  destruct A.
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
Qed.


(* Contradiction *)
Theorem contradiction : forall A, not (and A (not A)) = true.
Proof.
  intros A.
  destruct A.
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
Qed.


(* Excluded third *)
Theorem excluded_third : forall A, or A (not A) = true.
Proof.
  intros A.
  destruct A.
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
Qed.


(* Consequentia mirabilis / Clavius's law *)
Theorem consequentia_mirabilis : forall A, implication (implication (not A) A) A = true.
Proof.
  intros A.
  destruct A.
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
Qed.
