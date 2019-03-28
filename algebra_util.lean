import .logic_util
section add_group

lemma {u} add_group.ident_unique
  {G : Type u} [add_group G]
  (e : G) (h : ∀ x, x + e = x) : e = 0 :=
  eq.trans (eq.symm (zero_add e)) (h 0)

@[reducible]
def {u v} add_group.is_homomorphism
  {G : Type u} {H : Type v} [add_group G] [add_group H]
  (ψ : G → H) 
  := ∀ g g', ψ (g + g') = ψ g + ψ g'

lemma {u v} add_group.homomorphism_preserves_zero
  {G : Type u} {H : Type v} [add_group G] [add_group H]
  (ψ : G → H) (h : add_group.is_homomorphism ψ)
  : ψ 0 = 0 :=
begin
  apply @add_left_cancel _ _ (ψ 0),
  rw ← h, rw add_zero, rw add_zero
end

lemma {u v} add_group.homomorphism_preserves_neg
  {G : Type u} {H : Type v} [add_group G] [add_group H]
  (ψ : G → H) (h : add_group.is_homomorphism ψ)
  : ∀ g, ψ (- g) = - (ψ g) :=
begin
  intro, apply @add_left_cancel _ _ (ψ g),
  transitivity add_group.zero H,
  rw ← h, rw add_right_neg, 
  apply add_group.homomorphism_preserves_zero _ h,
  rw add_right_neg, refl
end

def {u v} kernel {G : Type u} {H : Type v} [add_group H]
  (ψ : G → H) := { g : G | ψ g = 0 }

lemma {u v} ker_trivial_imp_inj
  {G : Type u} {H : Type v} [add_group G] [add_group H]
  (ψ : G → H) (h : add_group.is_homomorphism ψ) :
  (∀ g, ψ g = 0 → g = 0) → function.injective ψ :=
begin
  intros ker_triv x y hxy, 
  have : ψ (x - y) = 0 :=
    calc ψ (x - y) = ψ (x + -y) : by rw sub_eq_add_neg
                ... = ψ x + ψ (-y) : h x (-y)
                ... = ψ x + -(ψ y) : by rw add_group.homomorphism_preserves_neg ψ h
                ... = ψ x + -(ψ x) : by rw hxy
                ... = 0 : by rw [← sub_eq_add_neg, sub_self],
  have : x - y = 0 := ker_triv _ this,
  rw ← sub_eq_zero_iff_eq, assumption
end

lemma {u v} inj_iff_ker_trivial
  {G : Type u} {H : Type v} [add_group G] [add_group H]
  (ψ : G → H) (h : add_group.is_homomorphism ψ) :
  function.injective ψ ↔ kernel ψ = { g : G | g = 0 } :=
begin
  constructor,
  { dunfold function.injective, intros ψ_inj,
    have : ∀ y, ψ y = 0 → y = 0,
    { intros, apply ψ_inj, rw a, symmetry,
      apply add_group.homomorphism_preserves_zero _ h },
    dsimp [kernel],
    funext, apply propext, constructor; intro h',
    { exact this _ h' },
    { rw (_ : g = 0),
      apply add_group.homomorphism_preserves_zero _ h,
      assumption } },
  { intros ker_triv, apply ker_trivial_imp_inj _ h,
    intros g h, rw (_ : ψ g = 0 ↔ g ∈ kernel ψ) at h,
    rw ker_triv at h, exact h, refl }
end

end add_group

section monoid

lemma {u} monoid.ident_unique
  {M : Type u} [monoid M]
  (e : M) (h : ∀ x, x * e = x) : e = 1 :=
  eq.trans (eq.symm (one_mul e)) (h 1)

@[reducible]
def {u v} monoid.is_homomorphism
  {M : Type u} {M' : Type v} [monoid M] [monoid M']
  (ψ : M → M') 
  := (∀ x y, ψ (x * y) = ψ x * ψ y) ∧ ψ 1 = 1

end monoid

section ring

lemma FOIL {R} [ring R] : ∀ a b c d : R, (a + b) * (c + d) = a*c + a*d + b*c + b*d :=
by { intros, rw [left_distrib, right_distrib, right_distrib], ac_refl }

@[reducible]
def {u v} ring.is_homomorphism
  {R : Type u} {S : Type v} [ring R] [ring S]
  (ψ : R → S) := add_group.is_homomorphism ψ
               ∧ monoid.is_homomorphism ψ 

@[reducible]
def {u v} ring.is_ismorphism
  {R : Type u} {S : Type v} [ring R] [ring S]
  (ψ : R → S) := ring.is_homomorphism ψ
               ∧ (∃ ψ', ring.is_homomorphism ψ'
                      ∧ ψ ∘ ψ' = id
                      ∧ ψ' ∘ ψ = id)

lemma {u v} classical.ring.bijective_homomorphism_is_isomorphism
  {R : Type u} {S : Type v} [ring R] [ring S]
  (ψ : R → S) : function.bijective ψ
              → ring.is_homomorphism ψ
              → ring.is_ismorphism ψ :=
begin
  intros h h', cases h with ψ_i ψ_s,
  dsimp [ring.is_ismorphism], constructor,
  assumption,
  cases classical.axiom_of_choice ψ_s with ψ',
  simp at h,
  have : ∀ x, ψ' (ψ x) = x,
  { intro x, apply ψ_i, apply h },
  existsi ψ', constructor,
  { constructor,
    { intros x y, rw [← h x, ← h y],
      rw ← h'.left, repeat { rw this } },
    constructor,
    { intros x y, rw [← h x, ← h y],
      rw ← h'.right.left, repeat { rw this } },
    { transitivity ψ' (ψ 1), congr, symmetry,
      exact h'.right.right, rw this } },
  { constructor; apply funext; assumption }
end

definition {u v} ring.isomorphic
  (R : Type u) (S : Type v) [ring R] [ring S]
  := ∃ ψ : R → S, ring.is_ismorphism ψ

infix ` ≅ `:50 := ring.isomorphic

@[symm]
lemma {u v} ring.isomorphic_symm
  (R : Type u) (S : Type v) [ring R] [ring S]
  : R ≅ S → S ≅ R
| ⟨ψ, ⟨h, ⟨ψ', ⟨h', k⟩⟩⟩⟩ := ⟨ψ', ⟨h', ⟨ψ, ⟨h, and.symm k⟩⟩⟩⟩

open classical

end ring