(* We can define our own boolean type *)
Inductive bool : Type :=
  | true
  | false.

Definition negb (b_0:bool) : bool :=
  match b_0 with
  | true => false
  | false => true
  end.

Definition andb (b_1:bool) (b_2:bool) : bool :=
  match b_1 with
  | true => b_2
  | false => false
  end.

Definition orb (b_1:bool) (b_2:bool) : bool :=
  match b_1 with
  | true => true
  | false => b_2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* We can also talk about conditionals *)
Definition negb' (b:bool) : bool := 
  if b then false
  else true.

Example test_negb: (negb' false) = true.
Proof. simpl. reflexivity. Qed.

(* Excercises *)
Definition nandb (b_1:bool) (b_2:bool) : bool :=
  negb (andb b_1 b_2).

Example test_nandb1: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
