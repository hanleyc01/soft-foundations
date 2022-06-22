Module NatPlayround.

  (* Representation of unary numbers is really simple *)

  Inductive nat : Type :=
    | O
    | S (n : nat).
  
  (* This definition ought to generate all natural integers,
      thus: 0 == 0
            1 == S 0
            2 == S ( S 0)
            3 == ..

     Another important note is how we have defined the constructor for
     S as being another thing of type nat as well, thus we can't have
     S true, only S a : nat
   *)
 
(* We can even define it using random identifiers;
   semantic interpretation is arbitrary about what these identifiers refer
   to. *)
  Inductive nat' : Type :=
    | stop 
    | tick ( foo : nat' ).


  Definition pred (n : nat) : nat :=
    match n with
    | O => O 
    | S n' => n'
    end.
  (* tick or S can be referred to as 'for some n, if n has the form S, then
     return n'*)
End NatPlayround.

(* Coq has some 'magic' in displaying natural numbers, even though
 they are defined as being the inductive proof*)

Check (S ( S ( S 0))). (* => 3 *)

Definition minustwo (n : nat) : nat :=
  match n with 
  | 0 => 0
  | S 0 => 0
  | S (S n') => n'
  end.

Compute (minustwo 4).

(* We can even do type checking  *)
Check S : nat -> nat.
Check pred : nat -> nat.
Check minustwo : nat -> nat. 

(* 
   The difference between S and the other functions is that
   S has no internal behavioral rules, S is simply a way to reperesent
   numbers.
 *)

(* We can also do recursion *)
Fixpoint even (n : nat) : bool := 
  match n with
  | 0 => true
  | S 0 => false
  | S ( S n') => even n'
  end.
  (* Recursive funcitons are defined using Fixpoint*)

Definition odd (n:nat) : bool :=
  negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed. (* Note that after the proof, our goal is gone *)

Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.

(* Multi-argument functions via recursion *)
Module NatPlayground2.

  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | 0 => m 
    | S (n') => S (plus n' m)
    end.

  Compute (plus 3 2).
  (*
     Computes as follows:
     plus 3 2 
     plus ( S ( S ( S 0))) ( S ( S 0))  by reduction
     S (plus S ( S (0))) (S (S 0))      per rule 2
     S (S (S (plus 0 (S (S 0)))          per rule 1 
     => S (S (S (S (S 0)))))
  *)
  Fixpoint mult (n m : nat) : nat :=
    match n with 
    | 0 => 0
    | S n' => plus m (mult n' m) 
        (* mult is recursive defined (Guarded on 1st arg)*)
    end.

    Example test_mult1: (mult 3 3) = 9.
    Proof. simpl. reflexivity. Qed.

  (* We can match on n objects by comma sep'ing them *)

  Fixpoint minus (n m : nat) : nat :=
    match n,m with
    | 0 , _ => 0
    | S _ , 0 => n 
    | S n', S m' => minus n' m'
    end.

  Fixpoint factorial (n:nat) : nat :=
    match n with
    | 0 => 1 
    | S n' => n * (factorial n')
    end.


  Example test_factorial1: (factorial 3) = 6.
  Proof. simpl. reflexivity. Qed.

End NatPlayground2.

(* 
We can also define for ease of access better notation. 
Note how we can define the precedence level, and the left or right
associativity.
*)
Notation "x + y" := (plus x y)
                        (at level 50, left associativity)
                        : nat_scope.
Notation "x - y" := (minus x y)
                        (at level 50, left associativity)
                        : nat_scope.
Notation "x * y" := (mult x y)
                        (at level 40, left associativity)
                        : nat_scope.

(*
Coq's standard library is incredibly small, and requires us to
define important functions like equality
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

Example test_leb1: 2 <=? 2 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2: 2 <=? 4 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb3: (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_eqb1: 3 =? 2 = false.
Proof. simpl. reflexivity. Qed.

Example test_eqb2: 3 =? 3 = true.
Proof. simpl. reflexivity. Qed.

Example test_eqb3: 2 =? 3 = false.
Proof. simpl. reflexivity. Qed.

(* Less than function *)
Fixpoint ltb (n m : nat) : bool :=
  match n with
  | 0 => match m with
         | 0 => false
         | _ => true
         end 
  | S n' => match m with 
            | 0 => false
            | S m' => (ltb n' m')
            end 
  end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_lib1: 2 <? 2 = false.
Proof. simpl. reflexivity. Qed.

Example test_lib2: 2 <? 4 = true.
Proof. simpl. reflexivity. Qed.

Example test_lib3: 4 <? 2 = false.
Proof. simpl. reflexivity. Qed.

