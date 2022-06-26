(*
 Polymorphism is the idea that functions can operate over over a 
   more abstract selection of types

   e.g., we've been working with lists over specific values,
   but what about lists over *all* types?
 *)

(* cf *)

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b: bool) (l: boollist).

(* Instead, we can generalize over all types *)
Inductive list (X:Type) : Type :=
  | nil 
  | cons (x : X) (l : list X).

(*
  What's unique about the type sig of list is that it 
   is a function from type to types 

   list : Type -> Type

   the X definition becomes part of its type signature

   Check (nil nat) => list nat
 *)

(*
Check nil : forall X : Type, list X.
*)

Fixpoint repeat (X : Type) (x : X) (count:nat) : list X := 
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 : 
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. simpl. reflexivity. Qed.

(* We can also talk deploy type-inference in our definitions
 of functions *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(* Coq is able to understand the type of X *)

Check repeat'. (* repeat' : forall X : Type, X -> nat -> list X *)
Check repeat. (* repeat : forall X : Type, X -> nat -> list X *)

(* Type inference is also powerful enough to allow us to define the functions without having to
   explicitly specificy the type listed every single time *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(* We can even define the function itself as having implicit types *)

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

Fixpoint app {X : Type } (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X:Type} (l:list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Notation "x :: y" := (cons x y)
                      (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).

Theorem app_nil_r : forall  (X : Type), forall l : list X,
    l ++ [] = l.
Proof.
  simpl. induction l as [| a l' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n. induction l as [| X l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2. induction l1 as [| A l IHl].
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.
