Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => negb b2
  | false => true
  end.
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb (andb b1 b2) b3.
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => 1
  | S n => S n * factorial n
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Definition ltb (n m : nat) : bool :=
  negb (leb m n).
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  rewrite <- H.
  intros H'.
  rewrite -> H'.
  reflexivity.
  Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
  Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros [] [].
  reflexivity.
  simpl.
  intros H.
  rewrite -> H.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  intros H.
  rewrite -> H.
  reflexivity.
  Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
  Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
  Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  rewrite -> H.
  rewrite -> H.
  destruct b.
  reflexivity.
  reflexivity.
  Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros [] [].
  reflexivity.
  simpl.
  intros H.
  rewrite -> H.
  reflexivity.
  simpl.
  intros H.
  rewrite -> H.
  reflexivity.
  reflexivity.
  Qed.

Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B Z
  | A n => B n
  | B n => A (incr n)
  end.

Fixpoint decr (m:bin) : bin :=
  match m with
  | Z => Z
  | A n => B (decr n)
  | B n => match n with
           | Z => Z
           | _ => A n
           end
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | A n => 2 * bin_to_nat n
  | B n => 1 + 2 * bin_to_nat n
  end.
