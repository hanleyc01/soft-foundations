(* Note that we can talk about binary numbers by introducing
   three new constructors; B0, B1, and the termination Z;
    3_10 == B1 (B1 Z)_2 == S (S (S 0)_1 *)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 m' => B1 m'
  | B1 m'' => B0 (incr m'')
  end.

Example bin_incr1: (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed. 

Example bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.

Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => O
  | B0 m' => 2 * (bin_to_nat m')
  | B1 m'' => 2 * (bin_to_nat m'') + 1 
  end.

Example test_bin_incr6: 
  bin_to_nat (B0 (B0 (B0 (B1 Z)))) = S (S (S (S (S (S (S (S O))))))).
Proof. simpl. reflexivity. Qed.
