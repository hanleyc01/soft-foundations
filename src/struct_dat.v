(*
   In inductive definitions, each constructor can take n number
   of arguments:
 *)
Inductive natprod : Type :=
  | pair (n_1 n_2 : nat).
(*
  This can be read as "The and only way to construct a pair of numbers
   is by apply the constructor pair to two arguments of type nat"
 *)
Check (pair 3 5 : natprod).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(*
  Note that pattern matchong on the pair is not to be confused with
   "multiple pattern syntax"
 *)
Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | 0    , _    => 0
  | S _  , 0    => n 
  | S n' , S m' => minus n' m' 
  end.

(*
  Some simple facts about pairs
 *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.
  (* Note that destruct only produces one subgoal*)
  (* This is because of the definition of natprod, it has only one constructor*)
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p.
  simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  simpl. reflexivity.
Qed.

(* 
  We can also generalize about lists of numbers
 *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

(* Like Haskell, we can introduce some notation *)
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* Some examples: *)
Definition mylist1 := 1 :: (2 :: ( 3 :: nil)).
Definition mylist2 := [1 ; 2 ; 3].

(* Functions for cons'ing and manipulating list*)
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | 0 => nil
      (* Take count = S count', then append n to the list *)
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => 0
      (* Drop h, and append S *)
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

(*
app [1;2;3] [1;2;3]
   1 :: app [2;3] [1;2;3] -> 
   1 :: 2 :: app [3] [1;2;3] -> 
   1 :: 2 :: 3 :: [1;2;3] ->
   1 :: 2 :: [3;1;2;3] ->
   1 :: [2;3;1;2;3] ->
   [1;2;3;1;2;3]
 *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof.
  simpl.
  reflexivity.
Qed.

(* We can also get head and tail functions*)
Definition head (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h 
  end.

Definition tail (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t 
  end.

Example test_hd1: head 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with 
  | nil => nil
  | h :: t => match h with
              | 0 => nonzeros t 
              | h' => h :: nonzeros t 
              end
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;0;3;0;4;0] = [1;2;3;4].
Proof.
  simpl.
  reflexivity.
Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | l1' , nil => l1'
  | nil , l2' => l2'
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
  end.

Example test_alternate: 
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof.
  simpl.
  reflexivity.
Qed.

(* Bags, or multisets, are lists in which elements can appear more than once*)
Definition bag := natlist.

Fixpoint equal(a b:nat): bool:=
match a, b with
| O, O => true
| S a', S b' => equal a' b'
| O, S b' => false
| S a', O => false
end.

Lemma eq_id: forall (a : nat), equal a a = true.
Proof.
  intros a. induction a as [| a' IHa'].
  - simpl. reflexivity.
  - simpl. apply IHa'.
Qed.
  

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with 
  | nil => 0
  | h :: t => match (equal h v) with
              | true => S (count v t)
              | false  => count v t
              end
  end.

Definition sum : bag -> bag -> bag := app.

Definition add (v : nat) (s : bag) : bag :=
  v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool :=
  match count v s with 
  | 0 => false
  | _ => true
  end.

Example test_mem1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_mem2: member 3 [1;2;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with 
  | nil => nil
  | h :: t => match (equal v h) with
              | true => t 
              | false => h :: remove_one v t 
              end
  end.

Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match (equal v h) with
              | true => remove_all v t 
              | false => h :: remove_all v t 
              end
  end.

Theorem add_inc_count: forall (v : nat) (s : bag),
  count v (add v s) = S (count v s).
Proof.
  intros v s. induction v as [| v' IHv'].
  - simpl. reflexivity.
  - simpl.
    assert (H : equal v' v' = true).
    { apply eq_id. }
    rewrite H.
    reflexivity.
Qed.

Theorem nil_app : forall l : natlist,
  nil ++ l = l.
Proof. simpl. reflexivity. Qed.

Theorem tl_length_pred : forall l : natlist,
  pred (length l) = length (tail l).
Proof.
  intros l. destruct l as [| n l'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Induction over lists involves the consideration of the list 
 as 1. l = nil , 2. l = cons n l' *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite IHl1'. reflexivity.
Qed.

Fixpoint rev (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Lemma app_len : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite IHl1'. reflexivity.
Qed.

Theorem rev_length_id : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite -> app_len.
    simpl. rewrite IHl'. 
    assert (H : forall n:nat, n + 1 = S n).
    { intros n'. induction n' as [| n'' IHn'']. 
      - simpl. reflexivity. 
      - simpl.  rewrite IHn''. reflexivity. }
    rewrite H. reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
  l ++ nil = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Theorem rev_app_distr : forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - rewrite -> app_nil_r. simpl. reflexivity.
  - simpl. rewrite -> IHl1'. rewrite -> app_assoc.
    reflexivity.
Qed.

Theorem rev_involutive: forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. simpl. rewrite IHl'.
    reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof. 
  intros l1 l2 l3 l4. rewrite app_assoc.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2  : natlist,
  nonzeros (l1 ++ l2) = nonzeros l1 ++ nonzeros l2.
Proof.
  intros l1 l2. induction l1 as [| n l IHl].
  - simpl. reflexivity.
  - simpl. case n.
    + simpl. apply IHl.
    + simpl. rewrite IHl. reflexivity.
Qed.

(* Maybe monad *)
Inductive natoption : Type := 
  | Some (n : nat)
  | None.

Fixpoint nth_error (l : natlist) ( n : nat) : natoption :=
  match l with
  | nil => None 
  | x :: xs => match n with
               | O => Some x
               | S n' => nth_error xs n'
               end
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d 
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None 
  | h :: t => Some h 
  end.

Example test_hd_error1 : hd_error nil = None.
Proof. reflexivity. Qed.


