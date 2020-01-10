Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite -> IHn.
  reflexivity.
  Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n.
  reflexivity.
  simpl.
  rewrite -> IHn.
  reflexivity.
  Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n.
  induction m.
  reflexivity.
  simpl.
  rewrite <- IHm.
  reflexivity.
  simpl.
  rewrite -> IHn.
  rewrite -> plus_n_Sm.
  reflexivity.
  Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  reflexivity.
  simpl.
  rewrite -> IHn.
  reflexivity.
  Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite -> IHn.
  rewrite -> plus_n_Sm with n n.
  reflexivity.
  Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  induction n.
  reflexivity.
  rewrite -> IHn.
  assert(H: forall a : bool, a = negb (negb a)).
  {
    intros [].
    reflexivity.
    reflexivity.
  }
  rewrite <- H.
  simpl.
  reflexivity.
  Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  assert(p + n = n + p).
  {
    rewrite -> plus_comm.
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
  Qed.

Theorem mult_dist : forall n m p : nat,
  p * (n + m) = p * n + p * m.
Proof.
  intros n m p.
  induction p.
  reflexivity.
  simpl.
  rewrite -> IHp.
  simpl.
  rewrite -> plus_assoc with (n + m) (p * n) (p * m).
  rewrite -> plus_assoc with (n + p * n) m (p * m).
  rewrite <- plus_assoc with n (p * n) m.
  rewrite -> plus_comm with (p * n) m.
  rewrite -> plus_assoc with n m (p * n).
  reflexivity.
  Qed.

Lemma mult_one_same : forall n : nat,
  n * 1 = n.
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite -> IHn.
  reflexivity.
  Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m.
  induction n.
  reflexivity.
  simpl.
  rewrite <- IHn.
  reflexivity.
  simpl.
  rewrite -> IHm.
  assert (H : n + n * m = n * 1 + n * m).
  {
    rewrite -> mult_one_same with n.
    reflexivity.
  }
  rewrite -> H.
  rewrite <- mult_dist with 1 m n.
  simpl.
  reflexivity.
  Qed.

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

Theorem leb_refl : forall n:nat,
  true = (n <=? n).
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite <- IHn.
  reflexivity.
  Qed.

Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  induction n.
  reflexivity.
  reflexivity.
  Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros [].
  reflexivity.
  reflexivity.
  Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p.
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHp. reflexivity.
  Qed.

Theorem S_nbeq_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  reflexivity.
  Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite -> plus_comm with n 0.
  reflexivity.
  Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros [] [].
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  rewrite -> mult_comm with (n + m) p.
  rewrite -> mult_comm with n p.
  rewrite -> mult_comm with m p.
  rewrite -> mult_dist with n m p.
  reflexivity.
  Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n.
  reflexivity.
  simpl.
  rewrite -> IHn.
  rewrite -> mult_plus_distr_r with m (n * m) p.
  reflexivity.
  Qed.

Theorem eqb_refl : forall n : nat,
  true = (n =? n).
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite <- IHn.
  reflexivity.
  Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  replace (p + n) with (n + p).
  reflexivity.
  rewrite -> plus_comm.
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

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | A n => 2 * bin_to_nat n
  | B n => 1 + 2 * bin_to_nat n
  end.

Theorem bin_to_nat_pres_incr : forall (b : bin),
  bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  induction b.
  reflexivity.
  reflexivity.
  simpl.
  rewrite -> IHb.
  simpl.
  rewrite <- plus_n_Sm.
  reflexivity.
  Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr(nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite -> bin_to_nat_pres_incr with (nat_to_bin n).
  rewrite -> IHn.
  reflexivity.
  Qed.
