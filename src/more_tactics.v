Theorem silly1 : forall n m : nat,
    n = m ->
    n = m.
Proof.
  intros n m eq.
  apply eq.
Qed.

(* The apply tactic works with conditional hypothesis and lemmas: if the statement being applied is an implication,
 then the premises of this implication will be added to the list of subgoals needed to be proved*)

Theorem silly2 : forall (n m o p : nat),
    n = m ->
    (n = m -> [n;o] = [m;p])
