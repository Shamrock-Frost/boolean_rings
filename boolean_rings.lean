import .logic_util .algebra_util
import .finite .partial_order_induction
import .sum_over

@[reducible]
def is_boolean (R) [ring R] : Prop := ∀ a : R, a * a = a

section
parameters {R : Type _} [ring R]

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

class boolean_ring (R) extends comm_ring (R) :=
(is_bool : is_boolean R)

lemma is_bool {R'} [boolean_ring R'] : ∀ a : R', a*a = a := boolean_ring.is_bool R'

def boolean_ring.mk2 (h : is_boolean R) : boolean_ring R := {
  mul_comm := boolean_ring.comm h,
  is_bool := h, 
  .._inst_1
}

open classical

instance pset.ring (T) : boolean_ring (set T) :=
{ boolean_ring .
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
                        all_goals { rw inter_comm, refl } },
  is_bool := by intros; apply inter_self
}
end

@[reducible] noncomputable
def sum_of {R : Type _} [comm_ring R] (h : finite R) (S : set R) : R :=
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

section
parameters {R : Type _} [ring R]
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
end

lemma sum_of_unique {R : Type _} [comm_ring R] (h : finite R) (S : set R)
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

section 

local attribute [instance] classical.prop_decidable

parameters {R : Type _} [boolean_ring R] (is_finite : finite R)

instance pseudo_subset_order
  : partial_order R :=
{ partial_order .
  le := λ x y, x*y = x,
  le_refl := by { intro, simp [(≤)], 
  rw is_bool a },
  le_trans := by { simp [(≤)], intros a b c hab hbc, 
    exact calc a * c = (a * b) * c : by { rw hab }
               ...   = a * (b * c) : mul_assoc _ _ _
               ...   = a * b       : by { rw hbc }
               ...   = a           : hab },
  le_antisymm := λ a b h1 h2,
    calc a   = a * b : eq.symm h1
         ... = b * a : mul_comm _ _
         ... = b     : h2
}

def orthogonal (x y : R) := x * y = 0

def min_nonzero.set :=
  { x : R | x ≠ 0 ∧ (∀ y, x ≤ y ∨ orthogonal x y) }

lemma min_nonzero_def2
  : min_nonzero.set = { x : R | x ≠ 0 ∧ (∀ y, y < x → y = 0) } :=
begin
  funext, apply propext, constructor,
  { intro h, cases h with h_ne_zero h_le_or_orthogonal,
    constructor, assumption, intros y hy,
    cases h_le_or_orthogonal y,
    { exfalso, apply hy.right, assumption },
    { transitivity x * y, symmetry, cases hy,
      rw mul_comm,
      assumption' } },
  { intro h, cases h with h_ne_zero h_minimal,
    apply and.intro h_ne_zero,
    intro y, 
    have h1 : (x * y) ≤ x,
    { refine (_ : (x * y)*x = x * y),
      rw mul_comm (x*y) x,
      rw ← mul_assoc, rw is_bool },
    by_cases (x ≤ (x * y)),
    { apply or.inl, apply le_antisymm; assumption },
    { apply or.inr, apply h_minimal,
      constructor; assumption }, }
end

lemma min_nonzero_def3 : min_nonzero.set = minimal (λ x, x ≠ 0) :=
by { rw min_nonzero_def2, dsimp [minimal], funext x,
     apply congr_arg (λ P, x ≠ 0 ∧ P),
     apply propext, constructor; intros h y; specialize h y;
     (`[rw ← classical.dne (y = 0)] <|> `[rw classical.dne (y = 0)]),
     assumption' }

def min_nonzero.type := subtype min_nonzero.set

lemma min_nonzero.orthogonal
  : ∀ (x y : min_nonzero.type), x ≠ y → x.val * y.val = 0 :=
begin
  dsimp [min_nonzero.type, min_nonzero.set], intros x y hxy,
  cases (x.property.right y.val); cases (y.property.right x.val),
  { exfalso, apply hxy, apply subtype.eq,
    transitivity x.val * y.val,
    symmetry, assumption,
    rw mul_comm, assumption },
  rw mul_comm, assumption'
end

lemma min_nonzero.orthogonal_contrapositive
  : ∀ {a b : min_nonzero.type}, ¬orthogonal a.val b.val → a = b :=
by { intros, apply classical.by_contradiction,
     intro, apply a_1, apply min_nonzero.orthogonal,
     assumption }

section pset_embed

noncomputable
def min_nonzero.pset_embed : set min_nonzero.type → R :=
 λ S, sum_of is_finite (subset_of_subtype_to_subset S)

lemma pset_embed_eq_sum_over :
  ∀ (S : set min_nonzero.type) 
    {n} (f : fin n → min_nonzero.type),
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
  : ∀ (S : set min_nonzero.type) (x0 : min_nonzero.type),
    x0 ∉ S → x0.val * min_nonzero.pset_embed S = 0 :=
begin
  intros S x0,
  have : set.finite S,
  { apply classical.sets_of_finite_types_are_finite,
    apply classical.subtypes_of_finite_types_are_finite,
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
      rw [elem_singleton, ( _ : x ∉ {y : min_nonzero.type | y = f ⟨size, _⟩}
                              ↔ x ≠ f ⟨size, _⟩)],
      tactic.swap, refl,
      rw ← f_s, constructor; intro h; cases h;
      constructor; assumption },
    rw left_distrib, rw min_nonzero.orthogonal,
    specialize ih { x ∈ S | x ≠ xn } _ _ ,
    rw (_ : fin.restrict (λ (n : fin (nat.succ size)), (f n).val)
          = (λ (n : fin size), (fin.restrict f n).val)),
    rw pset_embed_eq_sum_over { x ∈ S | x ≠ xn } f' at ih,
    rw [zero_add, ← ih],
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
  { apply classical.sets_of_finite_types_are_finite,
    apply classical.subtypes_of_finite_types_are_finite,
    assumption },
  cases this with A_size hA, cases hA with f hA, cases hA with f_i f_s,
  have : set.finite B,
  { apply classical.sets_of_finite_types_are_finite,
    apply classical.subtypes_of_finite_types_are_finite,
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
    rw [dif_pos _, dif_pos _]; assumption,
    rw [dif_neg _, dif_neg _]; assumption }
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
  { apply classical.sets_of_finite_types_are_finite,
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
  { congr, apply minus_subset_union_subset, assumption },
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
          rw union_decomp_l,
          rw sub_eq_add_neg, congr,
          symmetry, rw inter_comm,
          apply boolean_ring.neg_eq_self is_bool,
          rw disjoint_symm, apply minus_disj },
        { rw disjoint_symm,
          apply disjoint_implies_disjoint_subset ,
          apply inter_subset_r,
          rw disjoint_symm,
          apply minus_disj } },
      congr, exact decomp S' S },
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
  cases (classical.sets_of_finite_types_are_finite _ (classical.subtypes_of_finite_types_are_finite _ is_finite _) S) with n hn,
  cases hn with f hn, cases hn with f_i f_s,
  cases (classical.sets_of_finite_types_are_finite _ (classical.subtypes_of_finite_types_are_finite _ is_finite _) S') with m hm,
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
  have h2 : ∀ i, f i ∈ S' → (f i).val * sum_over (λ j, (g j).val) = (f i).val,
  { rw g_s, intros i h, specialize h2 i (eq.substr g_s h),
    cases h2 with j h2, cases h2 with hij hneq,
    rw mul_sum_over_left,
    rw sum_over_nonzero _ (λ _ : fin 1, (f i).val),
    { simp [sum_over] },
    { intros, apply g_i,
      transitivity (f i), rw mul_comm at a,
      apply min_nonzero.orthogonal_contrapositive a,
      have a' : (f i).val * (g y).val ≠ 0,
      rw ← a_1, assumption,
      apply min_nonzero.orthogonal_contrapositive a', },
    { intros x y _, apply fin1.singleton },
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
          rw min_nonzero.orthogonal_contrapositive this,
          apply eq.symm, apply is_bool (g w).val } } } },
  have h2' : ∀ i, f i ∉ S' → (f i).val * sum_over (λ j, (g j).val) = 0,
  { intros, rw mul_sum_over_left, rw ← sum_over_eq_zero,
    congr, funext, apply min_nonzero.orthogonal, intro h,
    apply a, rw h, rw g_s, existsi k, refl },
  transitivity sum_over (λ (i : fin n),
                ite (f i ∈ (S * S'))
                    (sum_over (λ (j : fin m), (f i).val * (g j).val))
                    0),
  { cases (classical.sets_of_finite_types_are_finite _ (classical.subtypes_of_finite_types_are_finite _ is_finite _) (S*S')) with k hk,
    cases hk with in_p hk, cases hk with in_p_i in_p_s, 
    rw pset_embed_eq_sum_over _ in_p in_p_i in_p_s,
    symmetry, apply sum_over_nonzero, 
    { intros x y hnez_x hxy, 
      apply f_i, apply subtype.eq,
      transitivity (ite (f x ∈ S * S') (sum_over (λ (j : fin m), (f x).val * (g j).val)) 0),
      { have mem1_x : f x ∈ S',
        { apply classical.by_contradiction, intro h,
          apply hnez_x, rw if_neg _, intro h', exact h h'.right, },
        have mem2_x : f x ∈ S,
        { rw f_s, existsi x, refl },
        have mem3_x : f x ∈ S * S' := ⟨mem2_x, mem1_x⟩,
        rw [if_pos _, ← mul_sum_over_left], symmetry, apply h2, exact mem1_x, exact mem3_x },
      transitivity (ite (f y ∈ S * S') (sum_over (λ (j : fin m), (f y).val * (g j).val)) 0),
      assumption,
      { have hnez_y : ite (f y ∈ S * S') (sum_over (λ (j : fin m), (f y).val * (g j).val)) 0 ≠ 0 := hxy ▸ hnez_x,
        have mem1_y : f y ∈ S',
        { apply classical.by_contradiction, intro h,
          apply hnez_y, rw if_neg _, intro h', exact h h'.right, },
        have mem2_y : f y ∈ S,
        { rw f_s, existsi y, refl },
        have mem3_y : f y ∈ S * S' := ⟨mem2_y, mem1_y⟩,
        rw [if_pos _, ← mul_sum_over_left], apply h2, exact mem1_y, exact mem3_y }},
    { intros x y hxy, apply in_p_i,
      apply subtype.eq, exact hxy },
    { transitivity { v | ∃ y : min_nonzero.type, y ∈ fun.im in_p ∧ v = y.val },
      { funext, apply propext, constructor; intro h; cases h,
        { existsi in_p h_w, constructor,
          existsi h_w, refl, symmetry, assumption },
        { cases h_h, cases h_h_left, existsi h_h_left_w,
          rw [h_h_right, ← h_h_left_h] } },
      transitivity { v | ∃ y : min_nonzero.type, y ∈ S * S' ∧ v = y.val },
      { funext, apply propext, constructor;
        intro h; cases h; existsi h_w; refine and.intro _ h_h.right,
        { rw in_p_s, exact h_h.left }, { rw ← in_p_s, exact h_h.left } },
      { funext, apply propext, constructor; intro h,
        { cases h, cases h_h, subst h_h_right, constructor,
          { have : h_w ∈ fun.im f := f_s ▸ h_h_left.left, cases this,
            existsi this_w, simp, subst this_h,
            rw if_pos h_h_left,
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
  { congr, funext, by_cases (f i ∈ S * S'),
    { rw if_pos, rw mul_sum_over_left, exact h },
    { rw if_neg, rw h2',
      { intro h', apply h, refine and.intro  _ h',
        rw f_s, existsi i, refl },
      exact h } }
end

lemma pset_embed_inj : function.injective min_nonzero.pset_embed :=
  ker_trivial_imp_inj min_nonzero.pset_embed 
                      pset_embed_preserves_add 
  $ λ S h, by {
    cases (classical.sets_of_finite_types_are_finite _ _ S),
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
    { apply classical.subtypes_of_finite_types_are_finite, assumption } }

noncomputable
def min_nonzero.proj : R → R :=
λ x, x * min_nonzero.pset_embed set.univ

lemma min_nonzero_proj_def2 {n} (f : fin n → R) (x : R)
  : function.injective f
  → min_nonzero.set = fun.im f
  → min_nonzero.proj x = sum_over (λ j, x * f j) :=
begin
  intros f_i f_s, dsimp [min_nonzero.proj],
  rw ← mul_sum_over_left, congr,
  have : ∀ j, min_nonzero.set (f j),
  { rw f_s, intro, existsi j, refl },
  rw pset_embed_eq_sum_over set.univ (λ j, ⟨f j, this j⟩),
  { intros i j h, apply f_i,
    rw ← subtype.mk.inj_eq, assumption },
  { funext, transitivity true, refl,
    apply propext, rw true_iff, cases a,
    rw f_s at a_property, cases a_property,
    existsi a_property_w, apply subtype.eq,
    assumption }
end

lemma min_nonzero_proj_def3
  : ∀ x, min_nonzero.proj x
       = min_nonzero.pset_embed {y : subtype min_nonzero.set | x * y.val ≠ 0} :=
begin
  intro x,
  have := classical.sets_of_finite_types_are_finite _  is_finite min_nonzero.set,
  destruct this, intros size h, cases h with f h, cases h with f_i f_s,
  rw min_nonzero_proj_def2 f x f_i f_s,
  { cases classical.subsets_of_finite_sets_are_finite (λ y (h : y ∈ min_nonzero.set ∧ x * y ≠ 0), h.left) this with size' h,
    cases h with g h, cases h with g_i g_s,
    rw sum_over_nonzero (λ j, x * f j) g,
    { have h1 : ∀ i, min_nonzero.set (g i),
      { have : ∀ i, fun.im g (g i) := λ i, ⟨i, rfl⟩,
        rw ← g_s at this, intro i, exact and.left (this i) },
      have h2 : ∀ i, x * (g i) ≠ 0,
      { have : ∀ i, fun.im g (g i) := λ i, ⟨i, rfl⟩,
        rw ← g_s at this, intro i, exact and.right (this i) },
      rw pset_embed_eq_sum_over _ (λ i, ⟨g i, h1 i⟩),
      { intros x y hxy, apply g_i,
        rw subtype.mk.inj_eq at hxy, assumption },
      { funext, apply propext, constructor; intro h,
        { have : fun.im g y.val, 
          rw ← g_s, constructor, apply y.property,
          assumption, cases this with k hk,
          existsi k, apply subtype.eq, exact hk },
        { cases h, rw ← h_h, apply h2 } } },
    { intros a b hnez hab, simp at hab ⊢,
      apply f_i, transitivity x * f a,
      { rw mul_comm,
        have hnez_a : f a * x ≠ 0,
        { rw mul_comm, exact hnez },
        have : min_nonzero.set (f a),
        { rw f_s, existsi a, refl },
        symmetry, refine or.resolve_right (this.right x) hnez_a },
      transitivity x * f b, exact hab,
      { rw mul_comm,
        have hnez_b : f b * x ≠ 0,
        { rw mul_comm, rw ← hab, exact hnez },
        have : min_nonzero.set (f b),
        { rw f_s, existsi b, refl },
        refine or.resolve_right (this.right x) hnez_b } },
  assumption, 
  { rw ← g_s, transitivity { t ∈ fun.im f | t * x = t },
    { funext, apply propext, constructor;
      rw ← f_s; intro h; apply and.intro h.left,
      { rw mul_comm at h,
        apply or.resolve_right (h.left.right x) h.right },
      { rw mul_comm,
        rw h.right, exact h.left.left } },
    { funext, apply propext, constructor; intro h,
      { cases h, destruct h_left, intros k hk, 
        rw ← f_s at h_left, constructor,
        { existsi k, simp, rw hk,
          rw mul_comm, assumption },
        { exact h_left.left } },
      { cases h, cases h_left with k hk, simp at hk,
        have : f k = a,
        { rw ← hk, symmetry,
          rw mul_comm,
          have : min_nonzero.set (f k),
          { rw f_s, existsi k, refl }, 
          apply or.resolve_right (this.right x),
          rw ← hk at h_right,
          rw mul_comm at h_right,
          exact h_right },
        rw ← this at hk ⊢, constructor, { existsi k, refl },
        rw mul_comm at hk, exact hk } } } }
end

lemma min_nonzero_proj_linear : ∀ x y,
  min_nonzero.proj (x + y) = min_nonzero.proj x + min_nonzero.proj y :=
begin
  intros,
  cases classical.sets_of_finite_types_are_finite _  is_finite min_nonzero.set with size h,
  cases h with f h, cases h with f_i f_s,
  repeat { rw min_nonzero_proj_def2 f _ f_i f_s },
  rw ← sum_over_sum, congr, funext, 
  apply right_distrib
end

lemma min_nonzero_proj_min_nonzero : ∀ x : min_nonzero.type,
  min_nonzero.proj x.val = x.val :=
begin
  intros,
  rw min_nonzero_proj_def3,
  rw (_ : {y : subtype min_nonzero.set | x.val * y.val ≠ 0} = { y | x = y }),
  rw pset_embed_eq_sum_over _ (λ j : fin 1, x),
  { simp [sum_over] },
  { intros x y _, apply fin1.singleton },
  { funext, apply propext, constructor; intro h,
    { existsi fin.mk 0 nat.zero_lt_one, assumption },
    { cases h, exact h_h } },
  { funext, apply propext, constructor; intro h,
    { apply min_nonzero.orthogonal_contrapositive, assumption },
    { rw (_ : x = y), suffices : y.val * y.val ≠ 0, exact this,
      rw is_bool y.val, exact y.property.left, assumption } }
end

lemma min_nonzero_proj_eq : ∀ x, min_nonzero.proj x = x :=
  have h1 : ∀ x y, orthogonal (x - x * y) y,
  from λ x y, calc (x - x * y) * y = x*y - (x*y)*y : mul_sub_right_distrib _ _ _
                   ...             = x*y - x*(y*y) : by rw mul_assoc
                   ...             = x*y - x*y     : by rw is_bool
                   ...             = 0             : sub_self _,
  have h2 : ∀ x y : R, x - x * y ≤ x,
  from λ x y, calc (x - x * y) * x = x*x - (x * y)*x   : mul_sub_right_distrib _ _ _
                   ...             = x*x - x * (x * y) : by rw mul_comm (x*y)
                   ...             = x*x - x*x*y       : by rw mul_assoc
                   ...             = x - x*y           : by rw is_bool,
  by {
    apply partial_order.induction, assumption',
    intros x ih,
    by_cases (x = 0),
    { rw h, rw min_nonzero_proj_def3,
      rw pset_embed_eq_sum_over _ fin.elim0,
      simp [sum_over], { intro a, exact a.elim0 },
      { funext, transitivity false; apply propext,
        { rw iff_false, simp, apply not_false },
        { rw false_iff, intro h, cases h, exact h_w.elim0 } } },
    cases partial_order.ex_min is_finite (λ r, r ≠ 0) x h with x' h',
    specialize h1 x x', specialize h2 x x',
    have h3 : min_nonzero.set x',
    { rw min_nonzero_def2,
      cases h'.left, constructor, assumption,
      intro y, rw classical.dne (y = 0), apply right },
    have h4 : x - x * x' < x,
    { apply lt_of_le_of_ne,
      assumption, intro h'', rw h'' at h1,
      apply h'.left.left, 
      transitivity x' * x, symmetry, exact h'.right,
      rw mul_comm, exact h1 },
    transitivity min_nonzero.proj (x - x * x' + x * x'),
    rw sub_add_cancel, rw min_nonzero_proj_linear,
    rw ih (x - x * x') h4,
    rw (_ : x * x' = x'),
    rw (_ : x' = (subtype.mk x' h3).val),
    rw min_nonzero_proj_min_nonzero, simp,
    rw mul_comm, exact h'.right }

lemma pset_embed_surj : function.surjective min_nonzero.pset_embed :=
begin
  dsimp [function.surjective],
  apply partial_order.induction (λ r, ∃ S, min_nonzero.pset_embed S = r) is_finite,
  intros x ih, simp * at ih,
  existsi { y | x * subtype.val y ≠ 0 },
  transitivity min_nonzero.proj x,
  { symmetry, apply min_nonzero_proj_def3 },
  apply min_nonzero_proj_eq
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