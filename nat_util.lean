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