(* 
   Not everything can be reduced via via simpl., as
   (as we have seen before), there are definitions of 
   functions which match against cases - thus our reasoning
   needs to account for all possible cases.

   Of course, our proofs cannot account for arbtirary values
   by themselves
 *)

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | 0 => match m with
         | 0 => true
         | S m' => false
         end 
  | S n' => match m with
            | 0 => false
            | S m' => eqb n' m'
            end 
  end.

(* Less-than-or-equal *)
Fixpoint leb (n m : nat) : bool :=
  match n with 
  | 0 => true
  | S n' => match m with 
            | 0 => false
            | S m' => leb n' m'
            end 
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation " x <=? y" := (leb x y) (at level 70) : nat_scope.

Theorem plus_1_neq_0_firstry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  destruct n as [| n'] eqn : E.
  - reflexivity.
  - reflexivity.
Qed.

(*
  The destruct function generates two subgoals, it is called an
  "intro pattern".

   In this case "|" represents 0, which is a null operator (0 
   takes no arguments), the next specifies n' as S n', "E" 
   tells the compiler that we are giving the name E, which 
   streamlines the subproofs

   Bullets are not necessary, as Coq will ask us to prove each
   subproof in turn, but it's still good form as it is more e
   explicit.
 *)

Definition andb (a b : bool) : bool :=
  match a with
  | false => false
  | _ => b 
  end.

Theorem andb_commutative : forall b c : bool, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb. (* Good style *)
  - destruct c eqn:Ec.
    + reflexivity. (* Note how we generate more proof goals *)
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.


(* We can also use curly braces to delimit subproofs *)
Theorem andb3_exchange :
  forall b c d : bool, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  - reflexivity.
  - rewrite <- H.
    destruct b.
    + reflexivity.
    + reflexivity.
Qed.
  
(* 
  Outline of proof:

   1. (forall b, c)(b && c)     Premise (Goal: c)
   2. x && y                    Universal instantiation (1.)
   3. y                         Conj. elimination (2.)
   4. x && y -> y               Cond. introduction (2.,3.)
   5. (forall b,c)(b && c -> c) Universal generalization (4.)
   Qed. (forall b,c)(b && c -> c)
*)


(* Note how we can introduce [|n] here, instead of destructing *)
Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

(* We don't even need to provide names *)
Theorem andb_commutative'' : forall b c,
  andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

(* 
  Point on recursion: all fixpoint functions require a termination at some
   point by ensuring that the terms are decreasing
 *)

Fixpoint plus' (n : nat) (m : mat) : nat :=
  match n with
  | 0 => m 
  | S n' => S (plus' n' m)
  end.
