
(* Notice in all the proofs how we use simpl. to simplify both sides of the 
 equation, and refelxivity. to check if both sides of the equation contain the
 same value*)

(* Our calls to reflexivity actually dind't need to include simpl. , as 
 reflevity is a much more powerful call*)

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem plus_0_n' : forall n : nat, 0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.

(* Reflexivity attempts to unfold the definitions, and replace them
   with their right-hand sides, but sometimes in the course of a proof,
   we might not want to unfold everything just at that point, so as to set a goal
  
   Also important to note that "Theorem", "Example", "Fact", "Remark",
   and "Lemma", are all synonyms to Coq.
*)

(* 
   Because we're saying that _for all n_, the proof involves introducing
   some arbitrary identifier n, (the intros n. clause). These are called
   _tactics_

 *)

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

(* We can also qualify our proofs with an antecedent that must hold*)
Theorem plus_id_example : forall n m : nat,
  n = m ->
  n + n = m + m.

Proof.
  intros p q.
  intros H.
  rewrite -> H. (* Simply tells coq to rewrite form l-to-r *)
  reflexivity.
Qed.

(* L-to-r rewrite is default, but we can do righ to left *)
Theorem plus_id_example' : forall n m : nat,
  n = m ->
  n + n = m + m.
Proof.
  intros p q.
  intros H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_id' : forall n m o : nat,
  n = m ->
  m = o ->
  n + m = m + o.
Proof.
  intros n m o.
  intros H_0 H_1.
  rewrite H_0.
  rewrite H_1.
  simpl.
  reflexivity.
Qed.

(* We can also check and use pre-proven theorems from the stdlib *)
Check mult_n_O.
(* ===> mult_n_O : forall n : nat, 0 = n * 0 *)
Check mult_n_Sm.
(* ===>  mult_n_Sm : forall n m : nat, n * m + n = n * S m *)

(* we can use them in further proofs *)
Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
  Show Proof.
Qed.
