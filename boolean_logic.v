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