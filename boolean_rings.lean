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
end transport_inj

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

def min_nonzero.set (is_bool : is_boolean R) :=
  { x : R | x ≠ 0 ∧ (∀ y, x*y = x ∨ x*y = 0) }

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

end pset_embed

end