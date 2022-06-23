Require Import Lia.
(* Unfortunately, because of the way that this proof is structured, 
 we are unable to use the regular tactics of simplification, destructuring,
 and reflexivity, as destructuring and simplification can lead to an arbitrary
 amount of proofs needed. *)

(* 
   To get around this, we can use induction, for example, a proof over natural numbers
   1. show that P(0) holds
   2. show that, for any n', if P(n') holds, then so does P(n');
   3. conclude that P(n) holds for all n
 *)
Theorem add_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0; 0 + 0 = 0 *) reflexivity.
  - (* n = S n' *) simpl.
    rewrite -> IHn'. reflexivity.
Qed.
(*
  Like destructuring, this takes as... as a clause, and the names of the variables
   are the names introduced for the usbgoals
   1. The first subgoal, n is replaced by S n',
   2. The second subgoal, IHn', is the case where n' + 0 = n'
   - the goal is to get S n' = (S n') + 0 proven, which simplifies to 
      S n' = S (n' + 0)
 *)

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.


Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n.
  reflexivity.
Qed.



Theorem minus_n_n : forall n, minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn']. 
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity. 
Qed.

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.


Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
   intros n m.
   induction n as [| n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite <- IHn'. reflexivity.
Qed.

Lemma add_id : forall m : nat, m = m + 0.
Proof.
  induction m as [| m' IHm'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHm'. reflexivity.
Qed.

Theorem add_commu : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n' IHn'].
  - simpl. apply add_id.
  - simpl. induction m.
    + simpl. rewrite add_0_r. reflexivity.
    + simpl. rewrite plus_n_Sm. rewrite IHn'.
      rewrite <- IHm. simpl. rewrite IHn'. reflexivity.
Qed.

Lemma succ_1_eq: forall n : nat,
  S n = 1 + n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'.
    reflexivity.
Qed.

(* While Coq is great at displaying formal proofs, we should not forget
  that we need to efficiently communicate proofs to even laymen! *)
(*
Theorem: (n =? n) = true, for all n : bool.

1. Let's consider the case where n = false,
    (false = false), this is tautological! therefore, this case is true
2. Let's consider the case wehre n = true,
    (true = true), and in the case, once more, true does indeed equal itself!
   Qed. n =? n always is a true judgment

 *)

Fixpoint double (n : nat) : nat :=
 match n with
 | 0 => 0 
 | S n' => S (S (double n'))
 end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm.
    reflexivity.
Qed.

(* Destruct differs from induction in that it deals with a finite amount
 of cases, whereas induction attempts to generalize over /every possible case/*)

(*
Sometimes it makes sense to not attempt to prove trivial results as its own
theorem, but rather prove it as a subproof, and this is done via the
assert tactic
 *)

Theorem mult_0_plus_ex : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(*
Oftentimes Coq's rewriting system is pretty dumb, so we need to prove things
with subproofs.
 *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H : n + m = m + n).
  { rewrite add_commu. reflexivity. }
  rewrite H. reflexivity.
Qed.
