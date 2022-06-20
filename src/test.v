(* Enumerated data tyoes :3*)
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(* Function definitions with pattern matching :3 *)
Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.


Compute (next_weekday friday).
(* => monday *)
Compute (next_weekday (next_weekday saturday)).
(* => monday => tuesday *)

(* Note how this adds to our subgoals; this is something which has been*)
(*/proven/ about our code, so fucking cool*)
(* We can say what we expect from Coq *)
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(* We can also ask coq to verify it *)
Proof. simpl. reflexivity. Qed.
