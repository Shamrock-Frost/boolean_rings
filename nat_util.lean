lemma nat.not_self_lt_lt_succ_self {a b : nat}
  : a < b → b < a + 1 → false :=
begin
  intros h1 h2, 
  cases nat.le.dest h1 with w h_1,
  cases nat.le.dest h2 with w_1 h_2,
  rw ← h_1 at h_2,
  rw ← nat.succ_add at h_2,
  apply nat.lt_irrefl (nat.succ a),
  apply nat.lt_of_lt_of_le,
  apply lt_add_of_pos_right (nat.succ a),
  refine (_ : nat.succ (w + w_1) > 0),
  apply nat.succ_pos,
  have : ∀ x y z, nat.succ x + y + z = x + nat.succ (y + z),
  { intros, rw ← nat.add_one, rw ← nat.add_one, ac_refl },
  rw this at h_2, rw h_2
end

def sub_lt_if_ge : ∀ n m k : ℕ, n ≤ k → k < n + m → k - n < m :=
begin
  intros n m k hnk h,
  rw ← nat.add_sub_of_le hnk at h,
  apply lt_of_add_lt_add_left h
end

def ge_if_not_lt {n k : ℕ} (h : ¬ (n < k)) : n ≥ k :=
by { cases nat.lt_or_ge n k, exfalso, exact h h_1, exact h_1 }

lemma pos_of_prod_pos_l {n m : ℕ} : 0 < n * m → 0 < n :=
begin
  intro h, apply decidable.by_contradiction, intro h',
  have : n = 0,
  { cases nat.lt_trichotomy n 0,
    { exfalso, apply nat.not_lt_zero _ h_1 },
    { cases h_1, assumption, trivial } },
  rw [this, zero_mul] at h, apply nat.lt_irrefl _ h,
end

lemma mod_of_add_multiple (n m k : ℕ) : (n + m * k) % m = n % m :=
begin
  induction k, simp,
  { have : m ≤ m * nat.succ k_n,
    { rw nat.mul_succ, apply nat.le_add_left },
    rw nat.mod_eq_sub_mod (nat.le_trans this (nat.le_add_left _ _)),
    rw nat.add_sub_assoc this,
    rw (_ : m * nat.succ k_n - m = m * nat.succ k_n - m * 1),
    rw ← nat.mul_sub_left_distrib, rw ← nat.add_one,
    rw nat.add_sub_cancel, assumption, simp }
end