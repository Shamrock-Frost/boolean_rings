import .logic_util .algebra_util
import .finite

@[reducible]
def is_boolean (R) [ring R] : Prop := ∀ a : R, a * a = a

section
parameters {R : Type _} [ring R]

def is_ring : ring R := by { exact _inst_1 }

lemma FOIL : ∀ a b c d : R, (a + b) * (c + d) = a*c + a*d + b*c + b*d :=
by { intros, rw [left_distrib, right_distrib, right_distrib], ac_refl }

lemma boolean_ring.has_char_2 (is_bool : is_boolean R) : ring.one R + ring.one R = 0 :=
begin
  suffices : (ring.one R + ring.one R) + (ring.one R + ring.one R) 
            = (ring.one R + ring.one R) + ring.zero R,
  { apply add_left_cancel, assumption },
  rw (_ : ring.one R + ring.one R + ring.zero R = ring.one R + ring.one R),
  transitivity (ring.one R + ring.one R)*(ring.one R + ring.one R),
  { rw FOIL, rw ring.mul_one, ac_refl },
  { apply is_bool },
  { rw ring.add_zero }
end

lemma boolean_ring.add_self_zero (is_bool : is_boolean R) : ∀ a : R, a + a = 0 :=
λ a, calc a + a = a * 1 + a * 1                 : by { rw mul_one a }
          ...   = a * (1 + 1)                   : eq.symm $ left_distrib a 1 1
          ...   = a * (ring.one R + ring.one R) : rfl
          ...   = a * 0                         : by { rw boolean_ring.has_char_2 is_bool }
          ...   = 0                             : mul_zero a

lemma boolean_ring.neg_eq_self (is_bool : is_boolean R) : ∀ a : R, a = -a :=
λ a, eq_neg_of_add_eq_zero $ boolean_ring.add_self_zero is_bool a

lemma boolean_ring.eq_if_add_zero (is_bool : is_boolean R) 
  : ∀ x y : R, x + y = 0 → x = y := by {
    intros,
    have : (x + y) + y = y, { rw a, apply zero_add },
    rw [add_assoc x y y,boolean_ring.add_self_zero is_bool, add_zero] at this,
    assumption
  }

theorem boolean_ring.comm (is_bool : is_boolean R) : ∀ (x y : R), x * y = y * x :=
begin
  intros x y,
  have h1 : x*y + y*x = x*y + x*y*x + y*x*y + y*x
       := calc x*y + y*x = (x*y + y*x)*(x*y + y*x) : eq.symm $ is_bool (x*y + y*x)
               ...       = (x*y)*(x*y) + (x*y)*(y*x) + (y*x)*(x*y) + (y*x)*(y*x) : by { apply FOIL }
               ...       = x * y + (x*y)*(y*x) + (y*x)*(x*y) + y*x : by { rw [is_bool (x*y), is_bool (y*x)] }
               ...       = x * y + x*y*x + (y*x)*(x*y) + y*x : by { rw (_ : (x*y)*(y*x) = x*(y*y)*x), rw is_bool y, repeat {rw mul_assoc}, } 
               ...       = x * y + x*y*x + y*x*y + y*x : by { rw (_ : (y*x)*(x*y) = y*(x*x)*y), rw is_bool x, repeat {rw mul_assoc}, },
  have h2 : x*y*x = y*x*y,
  { apply boolean_ring.eq_if_add_zero is_bool,
    have h21 := add_right_cancel h1,
    rw add_assoc at h21,
    have h22 : x*y + 0 = x * y + (x * y * x + y * x * y),
    { refine eq.trans _ h21, apply add_zero },
    exact eq.symm (add_left_cancel h22) },
  have h3 : x*y = x*y*x :=
    calc x*y = (x*y)*(x*y) : eq.symm $ is_bool (x*y)
         ... = x*(y*x*y)   : by { repeat { rw mul_assoc } }
         ... = x*(x*y*x)   : congr_arg _ $ eq.symm h2
         ... = (x*x)*y*x   : by { repeat { rw mul_assoc } }
         ... = x*y*x       : by { rw is_bool x },
  have h4 : y*x = y*x*y :=
    calc y*x = (y*x)*(y*x) : eq.symm $ is_bool (y*x)
         ... = y*(x*y*x)   : by { repeat { rw mul_assoc } }
         ... = y*(x*y)     : by { rw ← h3 }
         ... = y*x*y       : by { rw mul_assoc },
  rw [h3, h4], assumption
end

instance boolean_ring_is_comm_ring (is_bool : is_boolean R)
  : comm_ring R := { mul_comm := boolean_ring.comm is_bool, ..is_ring }

open classical

instance pset.ring (T) : comm_ring (set T) :=
{ comm_ring .
  add := (Δ),
  mul := (∩),
  one := set.univ,
  zero := ∅,
  neg := id,
  add_assoc := 
    λ A B C, @symm_diff_assoc T A B C
                (λ x, prop_decidable (A x))
                (λ x, prop_decidable (B x))
                (λ x, prop_decidable (C x)),
  add_comm := symm_diff_comm,
  mul_assoc := inter_assoc,
  mul_comm := inter_comm,
  zero_add := empty_symm_diff,
  add_zero := by { intro, rw symm_diff_comm, apply empty_symm_diff },
  mul_one := inter_univ,
  one_mul := by { intro, rw (_ : set.inter set.univ a = a ∩ set.univ), apply inter_univ, 
                  rw inter_comm, refl },
  add_left_neg := by { intro, simp, apply symm_diff_self },
  left_distrib := left_distrib_inter_symm_diff,
  right_distrib := by { intros, rw (_ : set.inter (a Δ b) c = c ∩ (a Δ b)),
                        rw (_ : set.inter a c = c ∩ a), rw (_ : set.inter b c = c ∩ b),
                        apply left_distrib_inter_symm_diff,
                        all_goals { rw inter_comm, refl }, }
}

theorem pset.is_boolean : ∀ T, is_boolean (set T) :=
begin
  unfold is_boolean, intros,
  rw (_ : a * a = a ∩ a),
  apply inter_self, refl
end

def sum_over : Π {n} (f : fin n → R), R
| 0     f := 0
| (n+1) f := sum_over (fin.restrict f) + f ⟨n, nat.lt_succ_self n⟩

lemma sum_over.step {n} (f : fin (nat.succ n) → R)
  : sum_over f = sum_over (fin.restrict f) + f ⟨n, nat.lt_succ_self n⟩
  := rfl

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
    cases prop_decidable (f ⟨n, nat.lt_succ_self n⟩ = 0),
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

lemma sum_unique.helper [comm_ring R] {n} (k : fin (nat.succ n))
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

lemma sum_over_unique [comm_ring R] {n} : ∀ (f g : fin n → R), same_embedding f g → sum_over f = sum_over g :=
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
    { transitivity @sum_over n (λ k, f ⟨k.val,nat.lt_trans k.is_lt $ nat.lt_succ_self n⟩)
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

@[reducible] noncomputable
def sum_of [comm_ring R] (h : finite R) (S : set R) : R :=
  sum_over
  $ classical.some
  $ classical.some_spec
  $ classical.sets_of_finite_types_are_finite R h S

section transport
universes u v
def eq.transport {A : Type u} (B : A → Type v) {a a' : A}
  : a = a' → B a → B a' := by { intros, cases a_1, assumption, }
lemma heq_transport {A : Type u} (B : A → Type v) {a b : A} (p : a = b)
  : ∀ b : B a, b == eq.transport B p b := by { intros, cases p, refl }
end transport
section transport_inj
universes u v w

lemma inj_implies_transport_inj {A : Type u} (B : A → Type v)
                                (C : A → Type w) {a a' : A}
                                (p : a = a')
  : ∀ f : B a → C a,
    function.injective f
    → function.injective (eq.transport (λ x, B x → C x) p f) :=
by { cases p, simp [eq.transport], intro, exact id }

lemma heq.funext1 {A : Type u} (B : Type v)
                              (C : A → Type w) {a a' : A}
                              (p : a = a')
  : ∀ (f : B → C a) (g : B → C a'), (∀ x, f x == g x) → f == g :=
by { cases p, intros, apply heq_of_eq, funext, apply eq_of_heq (a_1 x) }

lemma heq.funext {A : Type u} (B : A → Type v)
                              (C : Type w) {a a' : A}
                              (p : a = a')
  : (B a → false) → ∀ (f : B a → C) (g : B a' → C), f == g :=
by { cases p, intros,
     rw (_ : f = (λ b, false.elim (a_1 b))),
     rw (_ : g = (λ b, false.elim (a_1 b))),
     all_goals { funext, exfalso, exact a_1 x }, }

lemma sigma_eq_of_heq {A : Type u} (B : A → Type v)
                    : ∀ (a a' : A) (p : a = a')
                        (b : B a) (b' : B a'),
                      b == b' → sigma.mk a b = sigma.mk a' b' :=
by { intros, congr; assumption }

end transport_inj

lemma mul_sum_over_left 
  : ∀ {n} (f : fin n → R) a,
    a * sum_over f = sum_over (λ k, a * f k) :=
begin
  intros n, induction n; intros,
  { simp [sum_over] },
  case nat.succ : m ih { 
    simp [sum_over],
    rw left_distrib, congr, apply ih }
end

lemma mul_sum_over_right 
  : ∀ {n} (f : fin n → R) a,
    sum_over f * a = sum_over (λ k, f k * a) :=
begin
  intros n, induction n; intros,
  { simp [sum_over] },
  case nat.succ : m ih { 
    simp [sum_over],
    rw right_distrib, congr, apply ih }
end

lemma mul_sum_eq_double_sum
  : ∀ {n m} (f : fin n → R) (g : fin m → R),
    sum_over f * sum_over g
    = sum_over (λ i : fin n,
        sum_over (λ j : fin m, 
          f i * g j)) := 
by { intros, rw mul_sum_over_right, congr, funext, rw mul_sum_over_left }

-- I don't need this but it's neat ¯\_(ツ)_/¯
lemma mul_sum_eq_linear_sum
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
    apply congr,
    { apply congr_arg,
      dsimp [fin.restrict_many, fin.restrict],
      rw ih_m, refl, },
    { rw (_ : (λ (p : fin (n * nat.succ m)), f ((fin.line_to_square p).fst) * g ((fin.line_to_square p).snd))
            = (λ (p : fin (n * nat.succ m)), 
                (λ k : fin n × fin (nat.succ m), f (k.fst) * g (k.snd)) (fin.line_to_square p))),
      rw sum_over_tail, refl } }
end

lemma sum_of_unique [comm_ring R] (h : finite R) (S : set R)
  : ∀ n (f : fin n → R), 
      function.injective f
      → S = fun.im f
      → sum_of h S = sum_over f :=
begin
  intros n f f_i f_s,
  let h1 := classical.sets_of_finite_types_are_finite R h S,
  let n1 := classical.some h1,
  let h2 := classical.some_spec h1,
  let f1 : fin n1 → R := classical.some h2,
  let h3 := classical.some_spec h2,
  transitivity sum_over f1, refl,
  have : n1 = n, symmetry,
  apply one_way_to_be_finite S _ f _ f1 f_i f_s h3.left h3.right,
  suffices : (λ (s : Σ' (n : ℕ), (fin n → R)), sum_over s.snd) ⟨n1, f1⟩
           = (λ (s : Σ' (n : ℕ), (fin n → R)), sum_over s.snd) ⟨n, f⟩,
  { exact this },
  let f1' := eq.transport (λ (k : ℕ), fin k → R) this f1,
  have fheq : f1 == f1' := heq_transport (λ k, fin k → R) this f1,
  have : @psigma.mk nat (λ n, fin n → R) n1 f1
        = @psigma.mk nat (λ n, fin n → R) n f1',
  { congr; assumption },
  rw this, simp, apply sum_over_unique,
  have := @same_embedding_from_ims_eq (fin n) R,
  apply same_embedding_from_ims_eq f1' f,
  { apply inj_implies_transport_inj fin (λ _, R), exact h3.left },
  { assumption },
  rw ← f_s, rw h3.right, 
  symmetry, congr; assumption
end

instance pseudo_subset_order (is_bool : is_boolean R)
  : partial_order R :=
{ partial_order .
  le := λ x y, x*y = x,
  le_refl := by { intro, simp [(≤)], rw is_bool a },
  le_trans := by { simp [(≤)], intros a b c hab hbc, 
    exact calc a * c = (a * b) * c : by { rw hab }
               ...   = a * (b * c) : mul_assoc _ _ _
               ...   = a * b       : by { rw hbc }
               ...   = a           : hab },
  le_antisymm := λ a b h1 h2,
    calc a   = a * b : eq.symm h1
         ... = b * a : boolean_ring.comm is_bool _ _
         ... = b     : h2
}

lemma pseudo_subset_order.lt_of_le_and_ne (is_bool : is_boolean R)
  : ∀ x y : R, (@partial_order.le R (pseudo_subset_order is_bool) x y)
             → x ≠ y 
             → (@partial_order.lt R (pseudo_subset_order is_bool) x y) :=
begin
  intros, constructor, assumption, intro h, apply a_1,
  apply @partial_order.le_antisymm R (pseudo_subset_order is_bool); assumption
end

def orthongal (x y : R) := x * y = 0

def min_nonzero.set (is_bool : is_boolean R) :=
  { x : R | x ≠ 0 ∧
          (∀ y, (@partial_order.le R (pseudo_subset_order is_bool) x y)
              ∨ orthongal x y) }

lemma min_nonzero_def2 (is_bool : is_boolean R)
  : min_nonzero.set is_bool
  = { x : R | x ≠ 0 ∧ (∀ y, (@partial_order.lt R (pseudo_subset_order is_bool) y x) → y = 0) } :=
begin
  funext, apply propext, constructor,
  { intro h, cases h with h_ne_zero h_le_or_orthogonal,
    constructor, assumption, intros y hy,
    cases h_le_or_orthogonal y,
    { exfalso, apply hy.right, assumption },
    { transitivity x * y, symmetry, cases hy,
      rw boolean_ring.comm is_bool x y,
      all_goals {assumption} } },
  { intro h, cases h with h_ne_zero h_minimal,
    apply and.intro h_ne_zero,
    intro y, 
    have h1 : @partial_order.le R (pseudo_subset_order is_bool) (x * y) x,
    { refine (_ : (x * y)*x = x * y),
      rw boolean_ring.comm is_bool (x*y) x,
      rw ← mul_assoc, rw is_bool },
    cases (prop_decidable $ @partial_order.le R (pseudo_subset_order is_bool) x (x * y)),
    { apply or.inr, apply h_minimal,
      constructor; assumption },
    { apply or.inl,
      apply @partial_order.le_antisymm R (pseudo_subset_order is_bool);
      assumption } }
end

def min_nonzero.type (is_bool : is_boolean R) := 
  subtype (min_nonzero.set is_bool)

def min_nonzero.orthogonal (is_bool : is_boolean R)
  : ∀ (x y : min_nonzero.type is_bool), x ≠ y → x.val * y.val = 0 :=
begin
  dsimp [min_nonzero.type, min_nonzero.set], intros x y hxy,
  cases (x.property.right y.val); cases (y.property.right x.val),
  { exfalso, apply hxy, apply subtype.eq,
    transitivity x.val * y.val,
    symmetry, assumption,
    rw boolean_ring.comm is_bool, assumption },
  rw boolean_ring.comm is_bool,
  all_goals { assumption }
end

section pset_embed

parameters (is_bool : is_boolean R) (is_finite : finite R)

def R_comm : comm_ring R := boolean_ring_is_comm_ring is_bool

noncomputable
def min_nonzero.pset_embed : set (min_nonzero.type is_bool) → R :=
 λ S, @sum_of R_comm is_finite (subset_of_subtype_to_subset S)

lemma pset_embed_eq_sum_over :
  ∀ (S : set (min_nonzero.type is_bool)) 
    {n} (f : fin n → min_nonzero.type is_bool),
  function.injective f
  → S = fun.im f
  → min_nonzero.pset_embed S
    = sum_over (λ n, subtype.val $ f n) :=
begin
  intros S n f f_i f_s,
  dsimp [min_nonzero.pset_embed],
  apply @sum_of_unique,
  { intros x y hxy, apply f_i,
    apply subtype.eq, assumption },
  { rw f_s, dsimp [subset_of_subtype_to_subset],
    funext x, apply propext,
    constructor; intro h; cases h,
    { cases h_h, existsi h_h_w,
      rw (_ : x = (subtype.mk x h_w).val),
      rw ← h_h_h, refl },
    { rw ← h_h, simp, existsi (f h_w).property,
      existsi h_w, apply subtype.eq, refl } }
end

lemma min_nonzero_orthogonal_set
  : ∀ (S : set (min_nonzero.type is_bool)) (x0 : min_nonzero.type is_bool),
    x0 ∉ S → x0.val * min_nonzero.pset_embed S = 0 :=
begin
  intros S x0,
  have : set.finite S,
  { apply sets_of_finite_types_are_finite,
    apply subtypes_of_finite_types_are_finite,
    assumption },
  cases this with size h, revert S,
  induction size; intros; cases h with f h; cases h with f_i f_s,
  all_goals { rw pset_embed_eq_sum_over S f f_i f_s, simp [sum_over] },
  { rename a h', rename size_ih ih, rename size_n size,
    let xn := f ⟨size, nat.lt_succ_self size⟩,
    let f' := fin.restrict f,
    have : {x ∈ S | x ≠ xn} = fun.im f',
    { rw im_restrict _ _ f_i,
      funext x, apply propext,
      rw (_ : ({x ∈ S | x ≠ xn} x ↔ (fun.im f∖{f ⟨size, _⟩}) x)
            ↔ ((x ∈ S ∧ x ≠ xn) ↔ (fun.im f x ∧ x ∉ {f ⟨size, _⟩}))),
      tactic.swap, refl,
      rw [elem_singleton, ( _ : x ∉ {y : min_nonzero.type is_bool | y = f ⟨size, _⟩}
                              ↔ x ≠ f ⟨size, _⟩)],
      tactic.swap, refl,
      rw ← f_s, constructor; intro h; cases h;
      constructor; assumption },
    rw left_distrib, rw min_nonzero.orthogonal,
    specialize ih { x ∈ S | x ≠ xn } _ _ ,
    rw (_ : fin.restrict (λ (n : fin (nat.succ size)), (f n).val)
          = (λ (n : fin size), (fin.restrict f n).val)),
    rw pset_embed_eq_sum_over { x ∈ S | x ≠ xn } f' at ih,
    rw [add_zero, ← ih],
    { apply restrict_inj_if_fun_inj f f_i },
    { exact this },
    refl, existsi f',
    { constructor,
      apply restrict_inj_if_fun_inj f f_i,
      exact this },
    { intro h, apply h', exact h.left },
    { intro h, 
      have this' : f ⟨size, nat.lt_succ_self size⟩ ∈ fun.im f,
      existsi fin.mk size (nat.lt_succ_self size), refl,
      rw ← h at this', rw ← f_s at this',
      exact h' this' } }
end

lemma pset_embed_disj_union : ∀ A B, disjoint A B →
  min_nonzero.pset_embed (A ∪ B) = min_nonzero.pset_embed A + min_nonzero.pset_embed B :=
begin
  intros A B h, 
  have : set.finite A,
  { apply sets_of_finite_types_are_finite,
    apply subtypes_of_finite_types_are_finite,
    assumption },
  cases this with A_size hA, cases hA with f hA, cases hA with f_i f_s,
  have : set.finite B,
  { apply sets_of_finite_types_are_finite,
    apply subtypes_of_finite_types_are_finite,
    assumption },
  cases this with B_size hB, cases hB with g hB, cases hB with g_i g_s,
  have := union_size' h f g f_i f_s g_i g_s,
  rw pset_embed_eq_sum_over (A ∪ B) (fin.glue f g) this.left this.right,
  rw (_ : (λ (n : fin (A_size + B_size)), (fin.glue f g n).val)
        = fin.glue (λ n : fin A_size, (f n).val)
                   (λ n : fin B_size, (g n).val)),
  { rw sum_over_glue, apply congr, apply congr_arg,
    rw pset_embed_eq_sum_over A f f_i f_s,
    rw pset_embed_eq_sum_over B g g_i g_s },
  { dunfold fin.glue, funext,
    by_cases h : n.val < A_size,
    rw [dif_pos h, dif_pos h],
    rw [dif_neg h, dif_neg h] }
end

lemma pset_embed_minus_eq_minus : ∀ S S', S ⊆ S' →
  min_nonzero.pset_embed (S'∖S) = min_nonzero.pset_embed S' - min_nonzero.pset_embed S :=
begin
  intros S S' hsub,
  suffices : min_nonzero.pset_embed (S'∖S) + min_nonzero.pset_embed S = min_nonzero.pset_embed S',
  { exact calc min_nonzero.pset_embed (S'∖S)
                   = min_nonzero.pset_embed (S'∖S) + min_nonzero.pset_embed S - min_nonzero.pset_embed S
                   : eq.symm (add_sub_cancel _ _)
               ... = min_nonzero.pset_embed S' - min_nonzero.pset_embed S
                   : by { rw this } },
  have h1 : set.finite S',
  { apply sets_of_finite_types_are_finite,
    apply classical.subtypes_of_finite_types_are_finite R is_finite },
  have h2 : set.finite (S' ∖ S),
  { apply classical.subsets_of_finite_sets_are_finite (minus_is_subset _ _) h1 },
  cases h2 with minus_size h2,
  cases h2 with f_minus h2,
  have h3 : set.finite S,
  { apply classical.subsets_of_finite_sets_are_finite hsub h1 },
  cases h3 with sub_size h3,
  cases h3 with f_sub h3,
  have := union_size' (minus_disj _ _) f_minus f_sub h2.left h2.right h3.left h3.right,
  rw @minus_subset_union_subset _ _ _ (λ _, classical.prop_decidable _) hsub at this,
  cases this with f_i f_s,
  rw ← pset_embed_disj_union,
  { congr, apply @minus_subset_union_subset _ _ _ (λ _, prop_decidable _) hsub },
  apply minus_disj
end

lemma pset_embed_preserves_add : ∀ S S',
  min_nonzero.pset_embed (S + S')
  = min_nonzero.pset_embed S + min_nonzero.pset_embed S' :=
begin
  intros, rw (_ : S + S' = S Δ S'),
  { dsimp [(Δ)], rw pset_embed_minus_eq_minus,
    { rw (_ : min_nonzero.pset_embed S'
            = min_nonzero.pset_embed ((S'∖S) ∪ (S' ∩ S))),
      { rw pset_embed_disj_union (S'∖S),
        { rw ← add_assoc,
          rw ← pset_embed_disj_union,
          rw @union_decomp_l _ S S' (λ _, prop_decidable _),
          rw sub_eq_add_neg, congr,
          symmetry, rw inter_comm,
          apply boolean_ring.neg_eq_self is_bool,
          rw disjoint_symm, apply minus_disj },
        { rw disjoint_symm,
          apply disjoint_implies_disjoint_subset ,
          apply inter_subset_r,
          rw disjoint_symm,
          apply minus_disj } },
      congr, exact @decomp _ S' S (λ _, prop_decidable _) },
    exact (λ x hx, or.inl $ and.left hx) },
  refl
end

lemma pset_embed_preserves_zero : min_nonzero.pset_embed 0 = 0 :=
begin
  apply add_group.homomorphism_preserves_zero,
  exact pset_embed_preserves_add
end
set_option trace.check true

lemma pset_embed_preserves_mul
  : ∀ S S', min_nonzero.pset_embed (S * S') 
          = min_nonzero.pset_embed S * min_nonzero.pset_embed S' :=
begin
  intros,
  cases (sets_of_finite_types_are_finite _ (subtypes_of_finite_types_are_finite _ is_finite _) S) with n hn,
  cases hn with f hn, cases hn with f_i f_s,
  cases (sets_of_finite_types_are_finite _ (subtypes_of_finite_types_are_finite _ is_finite _) S') with m hm,
  cases hm with g hm, cases hm with g_i g_s,
  rw pset_embed_eq_sum_over S f, any_goals { assumption },
  rw pset_embed_eq_sum_over S' g, any_goals { assumption },
  rw mul_sum_over_right,
  have h1 : ∀ i j, f i ∉ S' → (f i).val * (g j).val = 0,
  { intros, apply min_nonzero.orthogonal, intro h,
    apply a, rw [h, g_s], existsi j, refl },
  have h1 : ∀ i, f i ∉ S' → (f i).val * sum_over (λ j, (g j).val) = 0,
  { intros, rw mul_sum_over_left, rw ← sum_over_eq_zero ,
    congr, funext, apply h1, assumption },
  have h2 : ∀ i, f i ∈ S' →
               ∃ j, (f i).val = (g j).val
                  ∧ ∀ j' ≠ j, (f i).val ≠ (g j').val,
  { intros, rw g_s at a, cases a with j hj,
    existsi j, constructor, symmetry, congr, assumption,
    rw ← hj, intro j', apply mt, intro, apply g_i,
    symmetry, apply subtype.eq, assumption },
  have orthog_contrapos
    : Π {a b : min_nonzero.type is_bool},
        ¬orthongal a.val b.val → a = b,
    { intros, apply classical.by_contradiction,
      intro, apply a_1, apply min_nonzero.orthogonal,
      assumption },
  have h2 : ∀ i, f i ∈ S' → (f i).val * sum_over (λ j, (g j).val) = (f i).val,
  { rw g_s, intros i h, specialize h2 i (eq.substr g_s h),
    cases h2 with j h2, cases h2 with hij hneq,
    rw mul_sum_over_left,
    rw sum_over_nonzero _ (λ _ : fin 1, (f i).val),
    { simp [sum_over] },
    { intros, apply g_i,
      transitivity (f i), rw boolean_ring.comm is_bool at a, apply orthog_contrapos a,
      have a' : (f i).val * (g y).val ≠ 0,
      rw ← a_1, assumption,
      apply orthog_contrapos a', },
    { suffices : ∀ x : fin 1, x.val = 0,
      intros x y _, apply fin.eq_of_veq,
      transitivity 0, apply this, symmetry, apply this,
      intros, cases x, simp, apply nat.eq_zero_of_le_zero,
      apply nat.le_of_succ_le_succ, exact x_is_lt },
    { simp [fun.im],
      transitivity { y | (f i).val = y },
      { funext, apply propext, constructor,
        { intro e, cases e, assumption },
        { intro h, rw (_ : (f i).val = b),
          existsi fin.mk 0 nat.zero_lt_one, refl, assumption } },
      { rw hij, funext, apply propext, constructor,
        { intro h, rw (_ : y = (g j).val),
          constructor, existsi j, apply is_bool,
          exact (g j).property.left, symmetry, assumption },
        { intro h, cases h.left, rw ← h_1,
          have : (g j).val * (g w).val ≠ 0, rw ← h_1 at h, apply h.right,
          rw orthog_contrapos this,
          apply eq.symm, apply is_bool (g w).val } } } },
  have h2' : ∀ i, f i ∉ S' → (f i).val * sum_over (λ j, (g j).val) = 0,
  { intros, rw mul_sum_over_left, rw ← @sum_over_eq_zero m,
    congr, funext, apply min_nonzero.orthogonal, intro h,
    apply a, rw h, rw g_s, existsi k, refl },
  transitivity sum_over (λ (i : fin n),
                @ite (f i ∈ (S * S')) (prop_decidable _) R
                     (sum_over (λ (j : fin m), (f i).val * (g j).val))
                     0),
  { cases (sets_of_finite_types_are_finite _ (subtypes_of_finite_types_are_finite _ is_finite _) (S*S')) with k hk,
    cases hk with in_p hk, cases hk with in_p_i in_p_s, 
    rw pset_embed_eq_sum_over _ in_p in_p_i in_p_s,
    symmetry, apply sum_over_nonzero, 
    { intros x y hnez_x hxy, 
      apply f_i, apply subtype.eq,
      transitivity (@ite (f x ∈ S * S') (prop_decidable _) R (sum_over (λ (j : fin m), (f x).val * (g j).val)) 0),
      { have mem1_x : f x ∈ S',
        { apply classical.by_contradiction, intro h,
          apply hnez_x, rw if_neg _, intro h', exact h h'.right, },
        have mem2_x : f x ∈ S,
        { rw f_s, existsi x, refl },
        have mem3_x : f x ∈ S * S' := ⟨mem2_x, mem1_x⟩,
        rw [if_pos _, ← mul_sum_over_left], symmetry, apply h2, exact mem1_x, exact mem3_x },
      transitivity (@ite (f y ∈ S * S') (prop_decidable _) R (sum_over (λ (j : fin m), (f y).val * (g j).val)) 0),
      assumption,
      { have hnez_y : @ite (f y ∈ S * S') (prop_decidable _) _ (sum_over (λ (j : fin m), (f y).val * (g j).val)) 0 ≠ 0 := hxy ▸ hnez_x,
        have mem1_y : f y ∈ S',
        { apply classical.by_contradiction, intro h,
          apply hnez_y, rw if_neg _, intro h', exact h h'.right, },
        have mem2_y : f y ∈ S,
        { rw f_s, existsi y, refl },
        have mem3_y : f y ∈ S * S' := ⟨mem2_y, mem1_y⟩,
        rw [if_pos _, ← mul_sum_over_left], apply h2, exact mem1_y, exact mem3_y }},
    { intros x y hxy, apply in_p_i,
      apply subtype.eq, exact hxy },
    { transitivity { v | ∃ y : min_nonzero.type is_bool, y ∈ fun.im in_p ∧ v = y.val },
      { funext, apply propext, constructor; intro h; cases h,
        { existsi in_p h_w, constructor,
          existsi h_w, refl, symmetry, assumption },
        { cases h_h, cases h_h_left, existsi h_h_left_w,
          rw [h_h_right, ← h_h_left_h] } },
      transitivity { v | ∃ y : min_nonzero.type is_bool, y ∈ S * S' ∧ v = y.val },
      { funext, apply propext, constructor;
        intro h; cases h; existsi h_w; refine and.intro _ h_h.right,
        { rw in_p_s, exact h_h.left }, { rw ← in_p_s, exact h_h.left } },
      { funext, apply propext, constructor; intro h,
        { cases h, cases h_h, subst h_h_right, constructor,
          { have : h_w ∈ fun.im f := f_s ▸ h_h_left.left, cases this,
            existsi this_w, simp, subst this_h,
            rw @if_pos _ (prop_decidable _) h_h_left,
            rw ← mul_sum_over_left, apply h2, exact h_h_left.right },
          exact h_w.property.left }, 
        { cases h, cases h_left, subst h_left_h, simp at h_right,
          have : f h_left_w ∈ S * S',
          { apply classical.by_contradiction, intro h,
            rw if_neg _ at h_right, apply h_right rfl,
            assumption },
          existsi f h_left_w, apply and.intro this,
          simp, rw if_pos _, rw ← mul_sum_over_left,
          apply h2, exact this.right, exact this } } } },
  { congr, funext, cases prop_decidable (f i ∈ S * S'),
    { rw if_neg _, rw h2',
      { intro h', apply h, refine and.intro  _ h',
        rw f_s, existsi i, refl },
      { exact h } },
    { rw if_pos, rw mul_sum_over_left, exact h } }
end

lemma pset_embed_inj : function.injective min_nonzero.pset_embed :=
  ker_trivial_imp_inj min_nonzero.pset_embed 
                      pset_embed_preserves_add 
  $ λ S h, by {
    cases (sets_of_finite_types_are_finite _ _ S),
    { revert S, induction w; intros,
      { apply has_size_zero_iff_empty _ h_1 },
      { cases h_1 with f, cases h_1_h with f_i f_s,
        let x0 := f ⟨w_n, nat.lt_succ_self _⟩,
        rw pset_embed_eq_sum_over S f f_i f_s at h,
        rw (_ : sum_over (λ (n : fin (nat.succ w_n)), (f n).val)
              = sum_over (λ (n : fin w_n), (fin.restrict f n).val) + x0.val) at h,
        rw (_ : sum_over (λ (n : fin w_n), (fin.restrict f n).val)
              = min_nonzero.pset_embed (S ∖ { x0 })) at h,
        { have : x0.val * min_nonzero.pset_embed (S∖{x0}) + x0.val * x0.val = x0.val * 0,
          rw [← left_distrib, h],
          rw is_bool x0.val at this,
          rw mul_zero at this,
          rw min_nonzero_orthogonal_set (S∖{x0}) x0 at this,
          have h' := h,
          rw zero_add at this, rw this at h,
          rw add_zero at h, exfalso,
          apply x0.property.left, assumption,
          intro h, apply h.right,
          rw elem_singleton, exact rfl },
        { rw pset_embed_eq_sum_over,
          { apply restrict_inj_if_fun_inj _ f_i },
          { rw [f_s, im_restrict], assumption } }, 
        refl } },
    { apply subtypes_of_finite_types_are_finite, assumption } }

lemma pset_embed_surj : function.surjective min_nonzero.pset_embed :=
begin
  admit
end

lemma pset_embed_preserves_one : min_nonzero.pset_embed 1 = 1 :=
begin
  apply monoid.ident_unique, intro x,
  cases (pset_embed_surj 1),
  cases (pset_embed_surj x),
  rw [← h_1, ← pset_embed_preserves_mul, mul_one]
end

end pset_embed

end