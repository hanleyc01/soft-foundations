(*
  Coq is a typed language, thus meaning that everything has a type!
  It's very familiar, type-tetris is such a fun little game :)
 *)

Check true.

Check false
  : bool.

(*
  Note how we can define types by other types.
 *)
Inductive rgb : Type :=
  | red
  | green (* The finite list of elements are called constructors*)
  | blue.

(* color.primary : rgb *)
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

(*
 Constructor expressions group together several constructors and denote
   that they belong to the same type set

  The type definition for color is:
   1. black is a color
   2. white is a color
   3. If p is a constructor of the rgb set, then the constructor
      primary applied to the argument p (or, primary p), is a constructor
      belonging to the set color
   5. These are the only things that can be a color
 *)

Definition isred ( c : color ) : bool :=
  match c with
  | primary red => true
  | _ => false
  end.

(* We can also enclose things within the module system *)

Module Playground.
  Definition b : rgb := blue.
End Playground.

(* Note the reuse of the identifier *)
Definition b : bool := true.

Check Playground.b : rgb.
