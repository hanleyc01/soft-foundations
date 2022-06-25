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


