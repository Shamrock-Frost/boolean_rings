import .sum_over .nat_util
section add_group

lemma {u} add_group.ident_unique
  {G : Type u} [add_group G]
  (e : G) (h : ∀ x, x + e = x) : e = 0 :=
  eq.trans (eq.symm (zero_add e)) (h 0)

lemma {u} add_group.inv_unique
  {G : Type u} [add_group G]
  (x x' : G) (h : x' + x = 0) : x' = -x :=
  iff.mp (@sub_eq_zero_iff_eq _ _ x' (-x))
    $ eq.symm (sub_neg_eq_add x' x) ▸ h

lemma {u} add_group.eq_zero_of_add_eq_self
  {G : Type u} [add_group G]
  {x : G} (h : x + x = x) : x = 0 :=
  add_left_cancel $ eq.trans h (eq.symm $ add_zero x)

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

@[reducible]
def {u} mul_n_times {M : Type u} [monoid M] : M → ℕ → M
| m 0     := 1
| m (n+1) := mul_n_times m n * m

section
universe u
instance monoid.pow {M : Type u} [monoid M] : has_pow M nat := ⟨mul_n_times⟩
end

lemma {u} monoid.exp_zero {M : Type u} [monoid M] (m : M)
  : m^0 = 1 := rfl

lemma {u} power_of_prod {M : Type u} [comm_monoid M]
  : ∀ (x y : M) (n : nat), (x * y)^n = x^n * y^n :=
begin
  intros, induction n; simp [(^), mul_n_times] at *,
  rw n_ih, ac_refl,
end

lemma {u} power_of_one {M : Type u} [monoid M]
  : ∀ (n : nat), 1^n = (1 : M) :=
by intros; induction n; simp [(^), mul_n_times] at *; rw n_ih

lemma {u} monoid.pow_of_sum_eq_mul {M : Type u} [monoid M]
  : ∀ (x : M) (n m : nat), x ^ (n+m) = x^n * x^m :=
begin
  intros, induction m with m ih;
  simp [(^), monoid.pow, mul_n_times] at *,
  rw nat.add_succ, dsimp [mul_n_times], rw ih,
  rw mul_assoc
end

lemma {u} monoid.pow_step_left {M : Type u} [monoid M]
  : ∀ (x : M) (n : nat), x ^ nat.succ n = x * x^n :=
begin
  intros, have : x = x^1, simp [(^), mul_n_times],
  transitivity x^1 * x^n,
  rw [this, ← monoid.pow_of_sum_eq_mul, nat.add_comm],
  congr, symmetry, assumption
end

lemma {u} exp_of_prod {M : Type u} [monoid M] 
  : ∀ (b : M) (n m : nat), b ^ (n*m) = (b^n)^m :=
begin
  intros, induction m with m ih;
  simp [(^), mul_n_times], simp [(^)] at ih,
  rw ← ih, rw [nat.mul_succ],
  transitivity b^(n * m + n), refl,
  rw monoid.pow_of_sum_eq_mul, refl,
end

lemma {u} comm_with_pow_if_comm {M : Type u} [monoid M]
  : ∀ (x y : M) (n : ℕ), x * y = y * x → x^n * y = y * x^n :=
begin
  simp [(^)], intros x y n comm,
  induction n with n ih, simp [mul_n_times],
  transitivity mul_n_times x n * x * y, refl,
  rw [mul_assoc, comm, ← mul_assoc, ih, mul_assoc]
end

lemma {u} pows_comm_if_comm {M : Type u} [monoid M]
  : ∀ (x y : M) (n m : ℕ), x * y = y * x → x^n * y^m = y^m * x^n :=
begin
  simp [(^)], intros x y n m comm,
  induction m with m ih,
  simp [mul_n_times],
  transitivity (mul_n_times x  n *  mul_n_times y m) * y, rw mul_assoc, 
  have := comm_with_pow_if_comm x y _ comm, dsimp [(^)] at this,
  rw [ih, mul_assoc, this, ← mul_assoc]
end

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

section semiring 

def {u} semiring.embed_nat
  {R : Type u} [semiring R] : nat → R
| 0     := 0
| (n+1) := semiring.embed_nat n + 1

lemma {u} semiring.embed_zero
  {R : Type u} [semiring R]
  : (semiring.embed_nat 0 : R) = 0 := rfl

lemma {u} semiring.embed_one
  {R : Type u} [semiring R]
  : (semiring.embed_nat 1 : R) = 1 :=
by intros; dsimp [semiring.embed_nat]; rw zero_add

lemma {u} semiring.embed_nat_sum
  {R : Type u} [semiring R]
  : ∀ (n m : nat),
    (semiring.embed_nat (n + m) : R)
  = semiring.embed_nat n + semiring.embed_nat m :=
begin
  intros, induction m with m ih,
  simp, rw [semiring.embed_zero, add_zero],
  rw nat.add_succ, dsimp [semiring.embed_nat],
  rw [← add_assoc, ih],
end

lemma {u} semiring.embed_nat_comm
  {R : Type u} [semiring R]
  : ∀ (x : R) n, x * semiring.embed_nat n
               = semiring.embed_nat n * x :=
begin
  intros, induction n with n ih;
  simp [semiring.embed_nat],
  rw [left_distrib, right_distrib], apply congr,
  rw ih, simp
end

def {u} binomial_expansion {R : Type u} [semiring R] : R → R → nat → R :=
λ x y n, sum_over (λ k : fin (n+1), semiring.embed_nat (binomial_coefficient n k.val) * x^k.val * y^(n - k.val))

lemma {u} binomial_theorem.helper1 {R : Type u} [semiring R]
  : ∀ (x y : R) n, x * binomial_expansion x y n
                 = sum_over (λ k : fin n, semiring.embed_nat (binomial_coefficient n k.val) * x^(k.val+1) * y^(n - k.val)) + x^(n+1) :=
begin
  intros, dsimp [binomial_expansion],
  rw mul_sum_over_left, rw [sum_over.step],
  apply congr,
  { apply congr_arg, congr, funext, cases k with k hk,
    simp [fin.restrict], rw [← mul_assoc x, ← mul_assoc x],
    rw semiring.embed_nat_comm, rw mul_assoc _ x,
    rw ← comm_with_pow_if_comm x x k rfl, refl },
  { simp, rw binomial_coefficient_self,
    simp [semiring.embed_nat], rw nat.sub_self,
    rw (_ : y^0 = 1), rw mul_one,
    rw ← comm_with_pow_if_comm x x n rfl,
    refl, refl }
end

lemma {u} binomial_theorem.helper2 {R : Type u} [semiring R]
  : ∀ (x y : R) n, x * y = y *x
  → y * binomial_expansion x y n
  = y^(n+1) + sum_over (λ k : fin n, semiring.embed_nat (binomial_coefficient n (k.val + 1)) * x^(k.val+1) * y^(n - k.val)) :=
begin
  intros x y n comm, dsimp [binomial_expansion],
  rw mul_sum_over_left, rw [sum_over.step_front],
  apply congr,
  { apply congr_arg, simp, rw binomial_coefficient_zero,
    simp [semiring.embed_nat],
    rw (_ : x^0 = 1), rw one_mul,
    rw ← comm_with_pow_if_comm y y n rfl,
    refl, refl },
  { congr, funext k, cases k with k hk,
    simp [fin.restrict],
    rw [← mul_assoc y, ← mul_assoc y],
    rw semiring.embed_nat_comm, rw mul_assoc _ y,
    rw ← comm_with_pow_if_comm x y (k+1) comm,
    rw mul_assoc, rw mul_assoc,
    rw [(_ : y * y ^ (n - nat.succ k) = y^(n-k)), mul_assoc],
    rw ← comm_with_pow_if_comm y y (n - nat.succ k) rfl,
    transitivity y ^(n - (nat.succ k) + 1), refl,
    apply congr_arg, transitivity nat.succ n- nat.succ k,
    rw [add_comm, ← nat.add_sub_assoc hk],
    congr, rw nat.one_add,
    rw [← nat.add_one, ← nat.add_one, nat.add_sub_add_right] },
end

lemma {u} binomial_theorem.helper3 {R : Type u} [semiring R]
  : ∀ (x y : R) n,
  binomial_expansion x y (n + 1)
  = x^(n+1) + sum_over (λ k : fin n, semiring.embed_nat (binomial_coefficient (n+1) (k.val + 1)) * x^(k.val+1) * y^(n - k.val)) + y^(n+1) :=
begin
  intros,
  dsimp [binomial_expansion],
  rw sum_over.step, simp,
  apply congr,
  { apply congr_arg, rw binomial_coefficient_self,
    rw [semiring.embed_one, one_mul, nat.sub_self],
    rw [monoid.exp_zero, mul_one] },
  rw sum_over.step_front,
  congr,
  { simp [fin.restrict], rw binomial_coefficient_zero,
    rw [semiring.embed_one, monoid.exp_zero], simp },
  funext k, simp [fin.restrict]
end

theorem {u} binomial_theorem {R : Type u} [semiring R]
  : ∀ x y : R, x * y = y * x
  → ∀ n, (x + y)^n = binomial_expansion x y n :=
begin
  intros x y comm n, induction n with n ih,
  { simp [(^), mul_n_times, binomial_expansion],
    dsimp [sum_over, sum_over], rw zero_add,
    simp [binomial_coefficient, mul_n_times, semiring.embed_nat] },
  rw [monoid.pow_step_left, right_distrib, ih],
  rw [binomial_theorem.helper1 x y n, binomial_theorem.helper2 x y n comm],
  transitivity (x^(n+1) +
                ((sum_over (λ (k : fin n), semiring.embed_nat (binomial_coefficient n (k.val)) * x ^ (k.val + 1) * y ^ (n - k.val)) + 
                  sum_over
                   (λ (k : fin n),
                     semiring.embed_nat (binomial_coefficient n (k.val + 1)) * x ^ (k.val + 1) * y ^ (n - k.val)))
                     + y ^ (n + 1))),
  { rw [add_comm _ (x^(n+1)), add_comm (y^(n+1)) _],
    rw [add_assoc, add_assoc] },
  rw ← sum_over_sum,
  rw (_ : (λ (k : fin n),
              semiring.embed_nat (binomial_coefficient n (k.val)) * x ^ (k.val + 1) * y ^ (n - k.val) +
                semiring.embed_nat (binomial_coefficient n (k.val + 1)) * x ^ (k.val + 1) * y ^ (n - k.val))
        = (λ (k : fin n),
              semiring.embed_nat (binomial_coefficient (n +  1) (k.val + 1)) * x ^ (k.val + 1) * y ^ (n - k.val))),
  { rw [binomial_theorem.helper3, add_assoc] }, 
  funext, dsimp [binomial_coefficient],
  rw semiring.embed_nat_sum, 
  rw [right_distrib, right_distrib, add_comm]
end

end semiring

section ring

lemma {u} FOIL {R : Type u} [ring R] : ∀ a b c d : R, (a + b) * (c + d) = a*c + a*d + b*c + b*d :=
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

def {u} neg_of_add {R : Type u} [ring R]
  (a b : R) : -(a + b) = -a + - b :=
begin
  rw [neg_eq_neg_one_mul, left_distrib],
  congr; rw ← neg_eq_neg_one_mul
end

def {u} elephant {R : Type u} [ring R]
  (a b : R) (n) :=
  sum_over (λ j : fin (n + 1), a^(n-j.val)*b^j.val)

lemma {u} elephant_teacup.helper1 {R : Type u} [ring R]
  (a b : R) (n) :
    elephant a b (n + 1)
    = a^(n+1) + (elephant a b n) * b :=
begin
  dsimp [elephant], rw sum_over.step_front,
  apply congr, { apply congr_arg, simp, apply mul_one },
  simp, rw mul_sum_over_right, congr, funext,
  rw mul_assoc, refl
end

lemma {u} elephant_teacup.helper2 {R : Type u} [ring R]
  (a b : R) (n) : elephant a b (n+1)
                = a * (elephant a b n) + b^(n+1) :=
begin
  dsimp [elephant], rw sum_over.step,
  apply congr, 
  { congr, rw mul_sum_over_left, congr,
    dsimp [fin.restrict], funext,
    rw ← mul_assoc, congr, rw (_ : n + 1 - k.val = (n - k.val) + 1),
    { rw [nat.add_comm, monoid.pow_of_sum_eq_mul],
      congr, simp [(^), mul_n_times] },
    { cases k, simp, rw nat.add_comm n 1, 
      rw nat.add_sub_assoc, apply nat.le_of_succ_le_succ k_is_lt } },
  simp, rw nat.sub_self n, simp [(^), mul_n_times]
end

lemma {u} elephant_teacup.helper3 {R : Type u} [ring R]
  (a b : R) (n) : a * b = b * a →
    b * elephant a b n
    = elephant a b n * b :=
begin
  intros h, induction n with n ih,
  { simp [elephant, sum_over,  (^), mul_n_times] },
  simp [elephant], rw [mul_sum_over_left, mul_sum_over_right],
  congr, funext,
  rw [← mul_assoc, ← comm_with_pow_if_comm a b _ h],
  rw mul_assoc, rw mul_assoc, apply congr_arg,
  rw comm_with_pow_if_comm, refl,
end

def {u} elephant_teacup {R : Type u} [ring R]
  (a b : R) (n) : a * b = b * a →
      a^(nat.succ (nat.succ n)) - b^(nat.succ (nat.succ n))
    = (a - b) * elephant a b (nat.succ n) :=
begin
  intros comm, rw mul_sub_right_distrib,
  transitivity a * (a^(n+1) + (elephant a b n) * b) - b * elephant a b (nat.succ n),
  rw elephant_teacup.helper2,
  { rw [left_distrib, left_distrib],
    rw [← elephant_teacup.helper3  _ _ _ comm, ← mul_assoc, ← mul_assoc],
    rw [← comm, sub_add_eq_sub_sub],
    rw [add_sub_assoc, sub_self, add_zero], 
    congr, transitivity a ^ n.succ * a, refl,
    rw comm_with_pow_if_comm, refl,
    transitivity b ^ n.succ * b, refl,
    rw comm_with_pow_if_comm, refl },
  rw elephant_teacup.helper1
end

end ring