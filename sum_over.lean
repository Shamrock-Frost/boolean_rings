import .finite .heq

section 
parameters {R : Type _} [semiring R]

def sum_over : Π {n} (f : fin n → R), R
| 0     f := 0
| (n+1) f := sum_over (fin.restrict f) + f ⟨n, nat.lt_succ_self n⟩

lemma sum_over.step {n} (f : fin (nat.succ n) → R)
  : sum_over f = sum_over (fin.restrict f) + f ⟨n, nat.lt_succ_self n⟩
  := rfl

lemma sum_over.step_front {n} (f : fin (nat.succ n) → R)
  : sum_over f = f  ⟨0, nat.zero_lt_succ n⟩ + sum_over (λ j : fin n, f ⟨nat.succ j.val, nat.succ_lt_succ j.is_lt⟩) :=
begin
  induction n with n ih, simp [sum_over],
  rw [sum_over.step, ih (fin.restrict f)],
  rw add_assoc, congr
end

lemma sum_over_split (n m) :
  ∀ (f : fin (n + m) → R),
    sum_over f =
    sum_over (fin.restrict_many n m f) + sum_over (fin.tail n m f) :=
begin
  induction m; intro f;
  simp [fin.restrict_many, fin.tail, sum_over],
  { congr, funext, congr, apply fin.eq_of_veq, refl },
  case nat.succ : m ih { 
    rw [add_comm (f ⟨n+m, _⟩), ← add_assoc],
    congr, apply ih }
end

lemma sum_over_eq_zero {n} : @sum_over n (λ _, 0) = 0 :=
by { induction n, refl, dsimp [sum_over], rw add_zero, apply n_ih }

lemma sum_over_omit {n} (f : fin (nat.succ n) → R)
  : ∀ k : fin (nat.succ n),
    sum_over f = sum_over (fin.fun_omit k.val f) + f k :=
begin
  revert f, induction n; intros f k,
  { dsimp [sum_over], congr, apply fin.eq_of_veq,
    symmetry, apply nat.eq_zero_of_le_zero,
    exact nat.le_of_succ_le_succ k.is_lt },
  case nat.succ : n ih {
    cases (_ : k.val < nat.succ n ∨ k.val = nat.succ n),
    { rw sum_over.step, rw ih _ ⟨k.val, h⟩,
      dsimp [sum_over], rw [add_assoc, add_assoc, add_comm (fin.restrict _ _)],
      congr, dsimp [fin.fun_omit], rw [dif_neg _],
      intro h', apply nat.not_self_lt_lt_succ_self h' h,
      simp [fin.restrict], congr, apply fin.eq_of_veq, refl },
    { rw h, rw (_ : f k = f ⟨nat.succ n, nat.lt_succ_self _⟩),
      dsimp [sum_over], congr, apply restrict_is_omit_n,
      rw restrict_is_omit_n, congr, apply fin.eq_of_veq, exact h },
    apply or.resolve_right, rw or_assoc,
    exact nat.lt_trichotomy k.val (nat.succ n),
    intro h', apply nat.not_self_lt_lt_succ_self h' k.is_lt }
end

lemma sum_over_nonzero {n} (f : fin n → R)
  : ∀ {m} (g : fin m → R),
    (∀ x y, f x ≠ 0 → f x = f y → x = y)
    → function.injective g
    → fun.im g = { x ∈ fun.im f | x ≠ 0 }
    → sum_over f = sum_over g :=
begin
  induction n; intros m g f_i g_i h,
  { intros, cases m, simp [sum_over],
    let k : fin m.succ := ⟨0, nat.zero_lt_succ m⟩,
    have : g k ∈ fun.im g := ⟨k, rfl⟩,
    rw h at this, cases this.left, exact w.elim0 },
  case nat.succ : n ih {
    dsimp [sum_over],
    cases classical.prop_decidable (f ⟨n, nat.lt_succ_self n⟩ = 0),
    tactic.swap,
    { rw h_1, rw add_zero, apply ih (fin.restrict f) g _ g_i, rw h,
      funext, apply propext, constructor; intro hx;
      refine and.intro _ hx.right; cases hx.left with k hk,
      { have : k.val < n,
        { cases (nat.lt_trichotomy k.val n), assumption,
          { exfalso, cases h_2,
            { apply hx.right, rw ← hk,
              rw ← h_1, congr, apply fin.eq_of_veq,
              assumption },
            { apply nat.not_self_lt_lt_succ_self h_2 k.is_lt } } },
        existsi fin.mk k.val this,
        dsimp [fin.restrict], rw ← hk,
        congr, apply fin.eq_of_veq, refl },
      { existsi (fin.mk k.val (lt_trans k.is_lt $ nat.lt_succ_self n)),
        rw ← hk, refl },
      { dsimp [fin.restrict], intros, apply fin.eq_of_veq,
        apply @fin.veq_of_eq (nat.succ n) ⟨x.val, nat.lt_trans x.is_lt (nat.lt_succ_self n)⟩
                                          ⟨y.val, nat.lt_trans y.is_lt (nat.lt_succ_self n)⟩,
        apply f_i; assumption } },
    { have : f ⟨n, nat.lt_succ_self n⟩ ∈ fun.im g,
      { rw h, refine and.intro _ h_1,
        existsi fin.mk n (nat.lt_succ_self n), refl },
      cases this with k hk, cases m, { exact k.elim0 },
      rw sum_over_omit g k, apply congr,
      rw ih _ (fin.fun_omit k.val g), 
      { dsimp [fin.restrict], intros, apply fin.eq_of_veq,
        apply @fin.veq_of_eq (nat.succ n) ⟨x.val, nat.lt_trans x.is_lt (nat.lt_succ_self n)⟩
                                          ⟨y.val, nat.lt_trans y.is_lt (nat.lt_succ_self n)⟩,
        apply f_i; assumption },
      { apply omit_inj_if_fun_inj, assumption },
      { rw im_omit _ _ _ g_i, rw hk,
        transitivity ({x : R | x ∈ fun.im f ∧ x ≠ 0} ∖ { f ⟨n, nat.lt_succ_self n⟩ }),
        { rw h, refl },
        { rw elem_singleton, funext x, apply propext,
          constructor; intro h'; cases h',
          { constructor, cases h'_left.left,
            have : w.val < n,
            cases nat.lt_trichotomy w.val n, assumption,
            cases h_3, exfalso, apply h'_right,
            rw ← h_2, congr, apply fin.eq_of_veq, exact h_3,
            exfalso, apply nat.not_self_lt_lt_succ_self h_3 w.is_lt,
            existsi fin.mk w.val this, rw ← h_2,
            dsimp [fin.restrict], congr, apply fin.eq_of_veq,
            refl, exact h'_left.right },
          { constructor, constructor, cases h'_left, 
            existsi fin.mk h'_left_w.val (nat.lt_trans h'_left_w.is_lt $ nat.lt_succ_self n),
            rw ← h'_left_h, dsimp [fin.restrict], congr,
            assumption, intro h', cases h'_left,
            apply nat.lt_irrefl n, rw (_ : n < n ↔ h'_left_w.val < n),
            exact h'_left_w.is_lt, rw (_ : h'_left_w.val = n),
            dsimp [fin.restrict] at h'_left_h h'_right,
            apply @fin.veq_of_eq (nat.succ n) ⟨h'_left_w.val, nat.lt_trans h'_left_w.is_lt (nat.lt_succ_self n)⟩
                                              ⟨n, nat.lt_succ_self n⟩,
            apply f_i, rw ← h'_left_h at h'_right,
            assumption, rw h'_left_h, assumption } } },
      { symmetry, assumption } } }
end

def sum_over_sum {n} : ∀ (f g : fin n → R),
  sum_over (λ k, f k + g k) = sum_over f + sum_over g :=
begin
  induction n; intros; simp [sum_over],
  rw [← add_assoc, add_comm],
  rw [← add_assoc (sum_over (fin.restrict f))],
  apply congr_fun (congr_arg _ $ n_ih _ _)
end

lemma sum_over_tail {n m} (h : fin n × fin (nat.succ m) → R)
  : sum_over
    (fin.tail (nat.mul n m) n
      (λ (p : fin (n * nat.succ m)),
        h (fin.line_to_square p)))
  = sum_over (λ k : fin n, h (k, ⟨m, nat.lt_succ_self m⟩)) :=
begin
  induction m,
  { congr, funext, 
    cases k, dsimp [fin.tail, fin.line_to_square],
    congr; rw (_ : nat.mul n 0 + k_val = k_val),
    apply nat.mod_eq_of_lt k_is_lt, tactic.swap,
    apply nat.div_eq_of_lt k_is_lt,
    all_goals { simp [nat.mul] } },
  case nat.succ : m ih {
    dsimp [fin.tail, fin.line_to_square],
    congr, funext, congr,
    { apply fin.eq_of_veq,
      simp [nat.mul], transitivity k.val % n,
      apply mod_of_add_multiple, apply nat.mod_eq_of_lt k.is_lt },
    { rw nat.div_eq_of_lt_le, rw mul_comm, apply nat.le_add_right,
      suffices : n * m + n + k.val < n * m + n + n,
      { rw nat.mul_comm, assumption },
      apply nat.add_lt_add_left, exact k.is_lt } }
end
end

section same_embedding
universes u v

structure same_embedding {A B} (f g : A → B) :=
(f_inj : function.injective f)
(g_inj : function.injective g)
(f2g : ∀ a, ∃ a', f a = g a')
(g2f : ∀ a, ∃ a', g a = f a')

lemma same_embedding_from_ims_eq {A : Type u} {B : Type v}
  : ∀ (f g : A → B),
    function.injective f
    → function.injective g
    → fun.im f = fun.im g
    → same_embedding f g :=
begin
  suffices : ∀ f g : A → B,
    fun.im f = fun.im g → ∀ a, ∃ a', f a = g a',
  { intros, constructor, 
    assumption, assumption,
    apply this, assumption,
    apply this, symmetry, assumption },
  intros f g h, intro a,
  have : f a ∈ fun.im f := ⟨a, rfl⟩,
  rw h at this, cases this with a' h,
  existsi a', symmetry, assumption
end

end same_embedding

section
parameters {R : Type _} [semiring R]

lemma sum_unique.helper {n} (k : fin (nat.succ n))
  : ∀ (f : fin (nat.succ n) → R), sum_over f = sum_over (fin.fun_omit k.val f) + f k :=
begin
  induction n,
  { intros, dsimp [sum_over],
    cases k, congr,
    have : k_val + 1 ≤ 1,
    { exact k_is_lt },
    have : k_val ≤ 0,
    { apply nat.le_of_succ_le_succ k_is_lt },
    symmetry, exact nat.eq_zero_of_le_zero this },
  case nat.succ : n ih { 
    intros,
    cases (nat.lt_trichotomy k.val n.succ),
    { rw (_ : sum_over f = fin.restrict f ⟨k.val, h⟩ + sum_over (fin.fun_omit k.val (fin.restrict f)) + f ⟨nat.succ n, nat.lt_succ_self n.succ⟩),
        rw add_assoc, rw add_comm,
        apply congr,
        { apply congr_arg, 
          simp [sum_over],
          rw (_ : fin.fun_omit (k.val) f ⟨n, _⟩ = f ⟨nat.succ n, _⟩),
          rw add_comm, congr,
          dsimp [fin.fun_omit],
          rw dif_neg, intro h',
          apply nat.not_self_lt_lt_succ_self h' h },
        { simp [fin.restrict], congr,
          apply fin.eq_of_veq, refl },
        { rw add_comm (fin.restrict _ _),
          rw ← ih ⟨k.val, h⟩, refl } },
      { cases h,
        { rw h, rw ← restrict_is_omit_n,
          rw (_ : f k = f ⟨nat.succ n, nat.lt_succ_self _⟩),
          refl, congr, apply fin.eq_of_veq, assumption },
        { exfalso, exact nat.not_self_lt_lt_succ_self h k.is_lt } } },
end

lemma sum_over_unique {n} : ∀ (f g : fin n → R), same_embedding f g → sum_over f = sum_over g :=
begin
  induction n,
  { intros, refl },
  case nat.succ : n ih { 
    intros,
    cases a with f_inj g_inj f2g g2f,
    have : ∃ k (h : k < n+1), f ⟨n, nat.lt_succ_self n⟩ = g ⟨k, h⟩, 
    { cases f2g ⟨n, nat.lt_succ_self n⟩,
      cases w,
      existsi w_val, existsi w_is_lt, assumption },
    cases this with k e, cases e with hlt h, 
    let g' : fin n → R := @fin.fun_omit R n k g,
    let f' : fin n → R :=
        λ m, f ⟨m.val, nat.lt_trans m.is_lt $ nat.lt_succ_self n⟩,
    specialize ih f' g' _,
    { transitivity @sum_over _ _ n (λ k, f ⟨k.val,nat.lt_trans k.is_lt $ nat.lt_succ_self n⟩)
                 + f ⟨n, nat.lt_succ_self n⟩,
      refl, rw h, rw sum_unique.helper ⟨k, hlt⟩ g,
      congr, transitivity sum_over f',
      refl, transitivity sum_over g',
      assumption, congr },
    { constructor,
      { intros x y hxy,
        cases x, cases y,
        simp [f'] at hxy,
        simp [fin.val] at hxy,
        apply fin.eq_of_veq,
        have := f_inj hxy,
        have := fin.mk.inj this,
        assumption },
      { apply omit_inj_if_fun_inj, assumption },
      { intros m,
        cases f2g ⟨m.val, nat.lt_trans m.is_lt $ nat.lt_succ_self n⟩,
        dsimp [g'],
        by_cases h' : w.val = k,
        { exfalso, apply nat.lt_irrefl n,
          have h' := eq.symm h',
          subst h', clear h',
          have : g w = g ⟨w.val, hlt⟩,
          { congr, apply fin.eq_of_veq, refl },
          rw this at h_1, rw ← h_1 at h,
          rw (_ : n < n ↔ m.val < n),
          exact m.is_lt, rw (_ : m.val = n),
          symmetry, apply fin.mk.inj,
          apply f_inj, exact h, },
        { by_cases h'' : w.val < k,
          { existsi fin.mk w.val (nat.lt_of_lt_of_le h'' (nat.le_of_lt_succ hlt)), 
            dsimp [fin.fun_omit],
            rw dif_pos h'', dsimp [f'],
            rw h_1, congr, apply fin.eq_of_veq, refl },
          { have h_2 : k < w.val,
            { cases lt_trichotomy k w.val,
              { exact h_2 },
              { exfalso, cases h_2,
                { apply h', symmetry, assumption },
                { apply h'', assumption } } },
            have h_3 : 0 < w.val,
            { apply nat.lt_of_le_of_lt,
              apply nat.zero_le, exact h_2 },
            existsi fin.mk (nat.pred w.val) _,
            { dsimp [fin.fun_omit],
              rw dif_neg _, simp [f'],
              rw h_1, congr, apply fin.eq_of_veq,
              simp [fin.val], rw nat.one_add,
              rw nat.succ_pred_eq_of_pos h_3, 
              intro h_4, cases w.val, cases h_2,
              simp at h_4, cases nat.eq_or_lt_of_not_lt h'',
              { exact h' h_5 }, 
              { exact nat.le_lt_antisymm (nat.succ_le_of_lt h_4) h_5, } },
            apply nat.lt_of_succ_lt_succ,
            rw nat.succ_pred_eq_of_pos h_3,
            exact w.is_lt } } },
      { intro m, by_cases hmk : m.val < k,
        { cases g2f ⟨m.val, nat.lt_trans m.is_lt $ nat.lt_succ_self n⟩,
          have : w.val < n,
          { by_contra,
            have : w.val = n,
            { apply or.resolve_right,
              apply eq_or_lt_of_not_lt a,
              apply nat.le_lt_antisymm,
              apply nat.le_of_lt_succ,
              exact w.is_lt },
            have : f w = g ⟨k, hlt⟩,
            { rw ← h, congr, apply fin.eq_of_veq, exact this },
            rw ← h_1 at this,
            have : m.val = k,
            { apply fin.mk.inj, apply g_inj, assumption },
            apply nat.lt_le_antisymm, exact hmk,
            apply le_of_eq, symmetry, assumption },
          existsi fin.mk w.val this,
          dsimp [f', g'],
          dsimp [fin.fun_omit],
          rw dif_pos hmk, rw h_1,
          congr, apply fin.eq_of_veq, refl },
        { cases g2f ⟨m.val + 1, nat.succ_lt_succ m.is_lt⟩,
          existsi fin.mk w.val _,
          dsimp [g', f'],
          dsimp [fin.fun_omit],
          rw dif_neg hmk,
          rw h_1, congr, apply fin.eq_of_veq, refl,
          have : w.val < n,
          { by_contra,
            have : w.val = n,
            { apply or.resolve_right,
              apply eq_or_lt_of_not_lt a,
              apply nat.le_lt_antisymm,
              apply nat.le_of_lt_succ,
              exact w.is_lt },
            have : f w = g ⟨k, hlt⟩,
            { rw ← h, congr, apply fin.eq_of_veq, exact this },
            rw ← h_1 at this,
            have : m.val + 1 = k,
            { apply fin.mk.inj, apply g_inj, assumption },
            apply hmk, rw ← this, apply nat.lt_succ_self, },
          exact this } } } }
end

lemma sum_over_glue {n m : ℕ}
  : ∀ (f : fin n → R) (g  : fin m → R),
    sum_over (fin.glue f g) = (sum_over f) + (sum_over g) :=
begin
  induction m,
  { intros, rw (_ : sum_over g = 0),
    { rw add_zero (sum_over f), congr, funext,
      dunfold fin.glue, rw dif_pos _,
      congr, apply fin.eq_of_veq, refl,
      clear f g, cases k, simp, rw add_zero at k_is_lt,
      assumption }, refl },
  case nat.succ : m ih {
    intros, 
    rw (_ : sum_over (fin.glue f g) = sum_over (fin.restrict $ fin.glue f g) + (fin.glue f g ⟨n+m, nat.lt_succ_self (n+m)⟩)),
    rw (_ : sum_over g = sum_over (fin.restrict g) + g ⟨m, nat.lt_succ_self m⟩),
    { rw ← add_assoc,
      apply congr, apply congr_arg,
      rw fin.restrict_glue_comm, apply ih,
      have h1 : ¬ (n + m < n),
      { intro h, apply nat.not_lt_zero m,
        rw [← add_zero n, add_assoc, zero_add] at h,
        apply nat.lt_of_add_lt_add_left h },
      dunfold fin.glue, rw [dif_neg h1],
      congr, apply nat.add_sub_cancel_left },
    all_goals {refl} }
end

end

lemma mul_sum_over_left {R : Type _} [semiring R]
  : ∀ {n} (f : fin n → R) a,
    a * sum_over f = sum_over (λ k, a * f k) :=
begin
  intros n, induction n; intros,
  { simp [sum_over] },
  case nat.succ : m ih { 
    simp [sum_over],
    rw [left_distrib],
    congr, apply ih }
end

lemma mul_sum_over_right {R : Type _} [semiring R]
  : ∀ {n} (f : fin n → R) a,
    sum_over f * a = sum_over (λ k, f k * a) :=
begin
  intros n, induction n; intros,
  { simp [sum_over] },
  case nat.succ : m ih { 
    simp [sum_over],
    rw [right_distrib],
    congr, apply ih }
end

lemma mul_sum_eq_double_sum {R : Type _} [ring R]
  : ∀ {n m} (f : fin n → R) (g : fin m → R),
    sum_over f * sum_over g
    = sum_over (λ i : fin n,
        sum_over (λ j : fin m, 
          f i * g j)) := 
by { intros, rw mul_sum_over_right, congr, funext, rw mul_sum_over_left }

-- @[reducible]
-- lemma double_sum_over_subset_indices {R : Type _} [ring R] {n m}
--   (S : set (fin n × fin m)) [decidable_pred S] (f : fin n × fin m → R) : R :=
--   sum_over (λ j : fin n, sum_over (λ k : fin m,
--     if S (j, k) then f (j, k) else 0))

-- lemma double_sum_param {R : Type _} [ring R] {n m k}
--   (S : set (fin n × fin m)) [decidable_pred S]
--   (f : fin n × fin m → R) (p : fin k → fin n × fin m)
--   : function.injective p → S = fun.im p
--   → double_sum_over_subset_indices S f = sum_over (f ∘ p) :=
-- begin
--   tactic.unfreeze_local_instances,
--   revert S, induction k with k ih; intros S _inst_2 p_i p_s,
--   { dunfold double_sum_over_subset_indices,
--     transitivity (0 : R), transitivity sum_over (λ j : fin n, (0 : R)),
--     congr, funext, transitivity sum_over (λ k : fin m, (0 : R)), congr, funext,
--     by_cases S (j,k), { rw p_s at h, cases h, exact h_w.elim0 }, { rw if_neg h },
--     apply @sum_over_eq_zero _ _ m, apply @sum_over_eq_zero _ _ n,
--     rw ← sum_over_eq_zero, congr, funext x, apply x.elim0 },
--   rw [sum_over.step, (_ : fin.restrict (f ∘ p) = f ∘ fin.restrict p)],
--   have : decidable_pred { y | S y ∧ y ≠ p ⟨k, nat.lt_succ_self k⟩ }, 
--   { intros y, by_cases y = p ⟨k, nat.lt_succ_self k⟩,
--     { apply is_false, intro h', exact h'.right h },
--     by_cases h' : S y, exact is_true (and.intro h' h), 
--     apply is_false, intro h, exact h' h.left },
--   rw ← @ih (fin.restrict p) { y | S y ∧ y ≠ p ⟨k, nat.lt_succ_self k⟩ } this,
--   dunfold double_sum_over_subset_indices,
--   --cases n with n, { exact (p ⟨k, nat.lt_succ_self k⟩).fst.elim0 },
--   --cases m with m, { exact (p ⟨k, nat.lt_succ_self k⟩).snd.elim0 },
--   { have : (f ∘ p) ⟨k, nat.lt_succ_self k⟩
--          = sum_over (λ j : fin n, if j = prod.fst (p ⟨k, nat.lt_succ_self k⟩)
--                                   then (f ∘ p) ⟨k, nat.lt_succ_self k⟩
--                                   else 0),
--     { clear _inst_2 p_s this S ih,
--       induction n with n ih,
--       { apply fin.elim0, apply prod.fst ∘ p, exact ⟨k, nat.lt_succ_self k⟩ },
--       rw sum_over.step, by_cases fin.mk n (nat.lt_succ_self n) = (p ⟨k, nat.lt_succ_self k⟩).fst,
--       { rw if_pos h, transitivity 0 + (f ∘ p) ⟨k, nat.lt_succ_self k⟩, rw zero_add,
--         congr, rw ← @sum_over_eq_zero _ _ n, congr, funext j,
--         simp [fin.restrict], rw ← h, rw if_neg,
--         rw sum_over_eq_zero, intro h, apply ne_of_lt j.is_lt, apply fin.veq_of_eq h },
--       { rw if_neg h, let p' := fin.restrict p,
        
        
--         } } }
-- end

/-

    *               *
   **     *         *
  *** =  ** ∪     ∪ * ∪
 ****   ***         *
*****        ****       *

   *              *
  **    *         *
 *** = ** ∪     ∪ * 
****        ***   *

Triangle(n+2) = Triangle(n) shifted up and right
              ∪ HorizontalLine(n)
              ∪ VerticalLine(n+1)
-/

lemma double_sum_triangle.helper1 {R :  Type _} [ring R]
  : ∀ {n : nat} (f : fin n.succ.succ → fin n.succ.succ → R),
    sum_over (λ i : fin n.succ.succ, sum_over (λ j : fin i.val.succ, f i ⟨j.val, lt_of_lt_of_le j.is_lt i.is_lt⟩))
  = sum_over (λ i : fin n.succ, sum_over (λ j : fin i.val,
    f ⟨i.val, nat.lt_trans i.is_lt (nat.lt_succ_self _)⟩
      ⟨j.val+1, nat.succ_lt_succ (lt_trans j.is_lt i.is_lt)⟩))
  + sum_over (λ i : fin n.succ, f ⟨i.val, lt_trans i.is_lt $ nat.lt_succ_self _⟩ ⟨0, nat.zero_lt_succ n.succ⟩)
  + sum_over (λ j : fin n.succ.succ, f ⟨n.succ, nat.lt_succ_self _⟩ ⟨j.val, j.is_lt⟩) :=
begin
  intros, rw [sum_over.step], dsimp [fin.restrict], congr,
  transitivity
  sum_over (λ (k : fin (nat.succ n)),
            f ⟨k.val, lt_trans k.is_lt (nat.lt_succ_self _)⟩
              ⟨0, nat.zero_lt_succ _⟩ +
            sum_over (λ (j : fin (k.val)),
                      f ⟨k.val, lt_trans k.is_lt (nat.lt_succ_self _)⟩
                        ⟨j.val + 1, nat.succ_lt_succ (lt_trans j.is_lt k.is_lt)⟩)),
  { congr, funext, rw sum_over.step_front },
  { rw [sum_over_sum, add_comm] }
end

lemma double_sum_triangle.helper2 {R :  Type _} [ring R]
  : ∀ {n : nat} (f : fin n.succ.succ → fin n.succ.succ → R),
    sum_over
      (λ (j : fin (nat.succ (nat.succ n))),
         sum_over (λ (i : fin (nat.succ (nat.succ n) - j.val)),
          f ⟨i.val + j.val, by { have h1 := nat.add_lt_add_right i.is_lt j.val, rw nat.sub_add_cancel (le_of_lt j.is_lt) at h1, exact h1 }⟩ j))
  = sum_over
      (λ (j : fin n.succ),
         sum_over (λ (i : fin (n.succ - j.val.succ)),
            f ⟨i.val + j.val.succ,
                by { have h1 := nat.add_lt_add_right i.is_lt j.val.succ,
                     rw nat.sub_add_cancel (nat.succ_le_of_lt j.is_lt) at h1,
                     transitivity n.succ, assumption, apply nat.lt_succ_self }⟩
              ⟨j.val.succ, nat.succ_lt_succ j.is_lt⟩))
  + sum_over (λ i : fin n.succ.succ, f ⟨i.val, i.is_lt⟩ ⟨0, nat.zero_lt_succ n.succ⟩)
  + sum_over (λ j : fin n.succ, f ⟨n.succ, nat.lt_succ_self _⟩ ⟨j.val.succ, nat.succ_lt_succ j.is_lt⟩) :=
begin
  intros, rw [sum_over.step_front],
  rw add_assoc, rw add_comm (sum_over (λ i : fin n.succ.succ, f ⟨i.val, i.is_lt⟩ ⟨0, nat.zero_lt_succ n.succ⟩)),
  rw add_comm, rw ← add_assoc, congr,
  transitivity
    sum_over
      (λ (j : fin n.succ),
         sum_over (λ (i : fin (n.succ.succ - j.val.succ)),
            f ⟨i.val + j.val.succ,
                by { have h1 := nat.add_lt_add_right i.is_lt j.val.succ,
                     rw nat.sub_add_cancel (le_of_lt (nat.succ_lt_succ j.is_lt)) at h1,
                     exact h1 }⟩
              ⟨j.val.succ, (nat.succ_lt_succ j.is_lt)⟩)),
  refl, rw ← sum_over_sum, congr, funext,
  transitivity sum_over
      (λ (i : fin (nat.succ (nat.succ n - nat.succ (j.val)))),
         f ⟨i.val + nat.succ (j.val),
              by { cases i with i i_is_lt, cases j with j j_is_lt, 
                   have h2 := i_is_lt, rw ← nat.succ_sub at h2,
                   have h3 := nat.add_lt_add_right h2 (nat.succ j),
                   rw nat.sub_add_cancel at h3, exact h3,
                   apply le_trans, exact j_is_lt, apply le_of_lt (nat.lt_succ_self _), exact j_is_lt }⟩
           ⟨nat.succ j.val, nat.succ_lt_succ j.is_lt⟩),
  have : nat.succ (nat.succ n) - nat.succ (j.val) = nat.succ (nat.succ n - nat.succ (j.val)),
  { rw nat.succ_sub, apply nat.succ_le_succ, apply nat.le_of_succ_le_succ j.is_lt },
  congr, exact this, { apply fin.funext R this, intro x, cases x, simp },
  rw sum_over.step, congr, dsimp,
  rw nat.sub_add_cancel, exact j.is_lt
end

lemma double_sum_triangle {R :  Type _} [ring R]
  : ∀ {n} (f : fin n → fin n → R), 
    sum_over (λ j : fin n, sum_over (λ k : fin j.val.succ, f j ⟨k.val, lt_of_lt_of_le k.is_lt j.is_lt⟩))
  = sum_over (λ k : fin n, sum_over (λ j : fin (n - k.val), f ⟨j.val + k.val, by { have h1 := nat.add_lt_add_right j.is_lt k.val, rw nat.sub_add_cancel (le_of_lt k.is_lt) at h1, exact h1, }⟩ k)) :=
begin
  apply nat.even_odd_induction
    (λ n, ∀ f : fin n → fin n → R,
     sum_over (λ j : fin n, sum_over (λ k : fin j.val.succ, f j ⟨k.val, lt_of_lt_of_le k.is_lt j.is_lt⟩))
     = sum_over (λ k : fin n, sum_over (λ j : fin (n - k.val), f ⟨j.val + k.val, by { have h1 := nat.add_lt_add_right j.is_lt k.val, rw nat.sub_add_cancel (le_of_lt k.is_lt) at h1, exact h1, }⟩ k))),
  intro f, simp [sum_over], simp [sum_over], intros n ih1 ih2 f,
  rw double_sum_triangle.helper1,
  rw double_sum_triangle.helper2,
  rw add_assoc, rw add_assoc, apply congr,
  { apply congr_arg, 
    transitivity sum_over (λ i : fin n, sum_over (λ j : fin i.val.succ,
      f ⟨i.val.succ, nat.succ_lt_succ (lt_trans i.is_lt (nat.lt_succ_self _))⟩
        ⟨j.val.succ, nat.lt_of_le_of_lt j.is_lt (nat.succ_lt_succ (lt_trans i.is_lt (nat.lt_succ_self _)))⟩)),
    rw sum_over.step_front, simp [sum_over],
    congr, funext, congr, funext, congr, rw add_comm,
    transitivity sum_over (λ i : fin n, sum_over (λ j : fin i.val.succ,
      (λ (i' j' : fin n), f ⟨i'.val+1, nat.succ_lt_succ (lt_trans i'.is_lt (nat.lt_succ_self _))⟩
                            ⟨j'.val+1, nat.succ_lt_succ (lt_trans j'.is_lt (nat.lt_succ_self _))⟩)
        i ⟨j.val, lt_of_lt_of_le j.is_lt i.is_lt⟩)),
    refl, rw ih1, rw sum_over.step, simp [fin.restrict], 
    symmetry, transitivity (0 : R) + sum_over
        (λ (k : fin n),
           sum_over
             (λ (i : fin (nat.succ n - nat.succ k.val)),
                f ⟨nat.succ (k.val) + i.val, by { have h1 := nat.add_lt_add_right i.is_lt k.val.succ, rw nat.sub_add_cancel (nat.succ_le_succ $ le_of_lt k.is_lt) at h1, rw add_comm,
                                                  apply lt_trans, exact h1, apply nat.lt_succ_self }⟩
                  ⟨nat.succ (k.val), lt_trans (nat.succ_lt_succ k.is_lt) (nat.lt_succ_self _)⟩)),
    { congr, transitivity sum_over (λ (i : fin (nat.succ n - nat.succ n)), f ⟨nat.succ n + i.val, _⟩ ⟨nat.succ n, _⟩),
      refl, transitivity sum_over (λ (i : fin 0), f ⟨nat.succ n + i.val, _⟩ ⟨nat.succ n, _⟩),
      congr, apply nat.sub_self, apply heq.funext, apply nat.sub_self, rw nat.sub_self, exact fin.elim0, 
      apply i.elim0, apply i.elim0, refl },
    { rw zero_add, congr, funext,
      have : nat.succ n - nat.succ k.val = n - k.val := nat.succ_sub_succ n k.val,
      apply dep_fn_eq_of_heq (λ m, fin m → R), exact this,
      apply fin.funext, { intro x, cases x, simp }, exact this } },
  { rw @sum_over.step _ _ n.succ,
    rw sum_over.step ((λ (j : fin (nat.succ n)), f ⟨nat.succ n, _⟩ ⟨nat.succ (j.val), _⟩)),
    rw ← add_assoc, rw ← add_assoc, apply congr_fun,
    apply congr_arg, rw @sum_over.step _ _ n.succ,
    dsimp [fin.restrict],
    rw add_assoc, congr, rw sum_over.step_front },
end

-- I don't need this but it's neat ¯\_(ツ)_/¯
lemma mul_sum_eq_linear_sum {R : Type _} [ring R]
  : ∀ {n m} (f : fin n → R) (g : fin m → R),
    sum_over f * sum_over g
    = sum_over (λ p : fin (n * m),
                let p' := fin.line_to_square p
                in f p'.fst * g p'.snd) :=
begin
  intros, rw mul_sum_eq_double_sum,
  induction m,
  { transitivity (0 : R), apply sum_over_eq_zero ,
    rw (_ : (λ (p : fin (n * 0)), let p' : fin n × fin 0 := fin.line_to_square p in f (p'.fst) * g (p'.snd))
          = (λ (p : fin (n * 0)), 0)),
    rw sum_over_eq_zero , funext, rw mul_zero at p, 
    apply p.elim0 },
  case nat.succ : m ih_m {
    simp [sum_over], 
    rw sum_over_sum,
    rw [sum_over_split],
    rw add_comm,
    apply congr,
    { apply congr_arg,
      dsimp [fin.restrict_many, fin.restrict],
      rw ih_m, refl, },
    { rw (_ : (λ (p : fin (n * nat.succ m)), f ((fin.line_to_square p).fst) * g ((fin.line_to_square p).snd))
            = (λ (p : fin (n * nat.succ m)), 
                (λ k : fin n × fin (nat.succ m), f (k.fst) * g (k.snd)) (fin.line_to_square p))),
      rw sum_over_tail, refl } }
end