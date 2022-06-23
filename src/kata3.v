Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS : forall n, even n -> even (S (S n)).

Inductive odd : nat -> Prop :=
| odd_1 : odd 1
| odd_SS : forall n, odd n -> odd (S (S n)).

(* Getting Started *)

Lemma even_add_one : forall n, even n -> odd (S n).
Proof. Admitted.

Lemma odd_add_one : forall n, odd n -> even (S n).
Proof. Admitted.

Lemma parity_dec : forall n, {even n} + {odd n}.
Proof. Admitted.

(* Addition *)

Theorem odd_add_odd : forall n m, odd n -> odd m -> even (n + m).
Proof. Admitted.

Theorem odd_add_even : forall n m, odd n -> even m -> odd (n + m).
Proof. Admitted.

Theorem even_add_odd : forall n m, even n -> odd m -> odd (n + m).
Proof. Admitted.

Theorem even_add_even : forall n m, even n -> even m -> even (n + m).
Proof. Admitted.

(* Multiplication *)

Theorem even_mul_even : forall n m, even n -> even m -> even (n * m).
Proof. Admitted.

Theorem even_mul_odd : forall n m, even n -> odd m -> even (n * m).
Proof. Admitted.

Theorem odd_mul_even : forall n m, odd n -> even m -> even (n * m).
Proof. Admitted.

Theorem odd_mul_odd : forall n m, odd n -> odd m -> odd (n * m).
Proof. Admitted.

Theorem even_mul : forall n m, even n -> even (n * m).
Proof. Admitted.

