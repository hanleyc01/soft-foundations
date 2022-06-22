Goal forall X Y : Prop, X -> Y -> X.

Proof.
  exact (fun X Y A B => A).
Qed.


Goal forall x y z : Prop, (x -> y) -> (y -> z) -> (x -> z).
Proof.
  intros x y z p q r.
  apply q.
  apply p.
  exact r.
  Show Proof.
Qed.

Goal forall x y z: Prop, (x -> y -> z) -> (x -> y) -> x -> z.
Proof.
  intros x y z a b c.
  apply a.
  Show Proof.
    - exact c.
  Show Proof.
    - apply b, c.
  Show Proof.
Qed.

Print Unnamed_thm1.
