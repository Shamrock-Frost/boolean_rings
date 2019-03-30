import .algebra_util

section definitions
variables {R : Type _} [ring R]

def is_nilpotent (x : R) := ∃ n : ℕ, x^n = 0
def is_unit (u : R) := ∃ v, u*v = 1

def sequence (A : Type _) := nat → A
def convolve (a b : sequence R) :=
  λ n, sum_over (λ j : fin (nat.succ n), a j.val * b (n - j.val))
infix ` ∗ `:70 := convolve

lemma convolution_assoc
  : ∀ a b c : sequence R, (a ∗ b) ∗ c = a ∗ (b ∗ c) :=
begin
  intros, funext, dsimp [(∗), (∗)],
  transitivity sum_over
      (λ (j : fin (nat.succ n)),
         sum_over (λ (j_1 : fin (nat.succ (j.val))), a (j_1.val) * b (j.val - j_1.val) * c (n - j.val))),
  { congr, funext, rw mul_sum_over_right },
  transitivity sum_over
      (λ (j : fin (nat.succ n)),
         sum_over (λ (j_1 : fin (nat.succ (n - j.val))), a (j.val) * (b (j_1.val) * c (n - j.val - j_1.val)))),
  { rw double_sum_triangle (λ (j j_1 : fin (nat.succ n)), a (j_1.val) * b (j.val - j_1.val) * c (n - j.val)),
    congr, funext,
    have : nat.succ n - k.val = nat.succ (n - k.val),
    rw nat.succ_sub (nat.le_of_succ_le_succ k.is_lt),
    congr, funext, exact this, apply fin.funext _ this, 
    intro x, cases x, simp *,
    rw nat.add_sub_cancel, rw ← mul_assoc, apply congr_arg,
    apply congr_arg, rw nat.sub_sub, rw add_comm },
  { congr, funext, rw mul_sum_over_left }
end

structure power_series (R' : Type _) :=
(coefficients : sequence R')

lemma power_series.eq {R' : Type _}
  : ∀ p q : power_series R',
    (∀ n, p.coefficients n = q.coefficients n) 
  → p = q
| (power_series.mk a) (power_series.mk b) :=
  λ h, congr_arg power_series.mk (funext h)

postfix `[[x]]`:100 := power_series

def power_series.zero_coeff : sequence R := λ _, 0
def power_series.one_coeff : sequence R
| 0 := 1
| (nat.succ _) := 0
lemma power_series.one_coeff_of_pos
  : ∀ {n}, 0 < n → power_series.one_coeff n = (0 : R) :=
by { intros, cases n, exfalso, exact lt_irrefl 0 a, refl }

meta def power_series_preamble := 
`[intros, apply power_series.eq, intro, dsimp [power_series.coefficients]]

instance : ring (R[[x]]) := { ring .
  zero := power_series.mk power_series.zero_coeff,
  one  := power_series.mk power_series.one_coeff,
  add  := λ p q, power_series.mk (λ n, p.coefficients n + q.coefficients n),
  neg  := λ p, power_series.mk (λ n, - p.coefficients n),
  mul  := λ p q, power_series.mk (convolve p.coefficients q.coefficients),
  zero_add := by { power_series_preamble, apply zero_add },
  add_zero := by { power_series_preamble, apply add_zero },
  add_left_neg := by { power_series_preamble, apply add_left_neg },
  add_assoc := by { power_series_preamble, apply add_assoc },
  add_comm := by { power_series_preamble, apply add_comm },
  mul_assoc := by { intros, cases a, cases b, cases c,
                    dsimp [power_series.coefficients], rw convolution_assoc },
  one_mul := by { power_series_preamble, dsimp [(∗)],
                  rw sum_over.step_front, dsimp [power_series.one_coeff],
                  rw one_mul, transitivity a.coefficients n + 0, congr,
                  rw ← sum_over_eq_zero, congr, funext,
                  transitivity 0 * a.coefficients (n - nat.succ (j.val)),
                  congr, apply sum_over_eq_zero, apply zero_mul, apply add_zero },
  mul_one := by { power_series_preamble, dsimp [(∗)], 
                  rw sum_over.step, rw nat.sub_self, dsimp [power_series.one_coeff],
                  rw mul_one, transitivity 0 + a.coefficients n, congr,
                  rw ← sum_over_eq_zero, congr, funext, dsimp [fin.restrict],
                  transitivity a.coefficients k.val * 0, congr,
                  rw power_series.one_coeff_of_pos (nat.sub_pos_of_lt k.is_lt),
                  apply mul_zero, apply zero_add },
  left_distrib := by { power_series_preamble, dsimp [(∗)],
                       rw ← sum_over_sum, congr, funext, apply left_distrib },
  right_distrib := by { power_series_preamble, dsimp [(∗)],
                       rw ← sum_over_sum, congr, funext, apply right_distrib } }

end definitions

section lemmas
variables {R : Type _} [ring R]

lemma my_mul_zero : ∀ x : R, x * 0 = 0 :=
λ x, add_group.eq_zero_of_add_eq_self $ eq.symm $
     calc x * 0 = x * (0 + 0)   : by rw zero_add
          ...   = x * 0 + x * 0 : left_distrib _ _ _

end lemmas

namespace problem1 section
parameters {R : Type _} [ring R]

lemma a : 1 * 1 = (1 : R) := mul_one 1

lemma b : (- 1) * (- 1) = (1 : R) :=
  have (-1)*(-1) = -(-1 : R),
  from add_group.inv_unique (-1 : R) (-1 * -1)
       $ calc -1 * (-1 : R) + -1 = -1 * -1 + -1 * 1 : by rw mul_one
             ...                = (-1) * (-1 + 1)   : by rw eq.symm (left_distrib (-1 : R) (-1) 1)
             ...                = (-1) * 0          : by rw [neg_add_eq_sub, sub_self]
             ...                = 0                 : my_mul_zero (-1),
  show (-1 : R) * (-1) = 1, from eq.trans this $ neg_neg (1 : R)
end end problem1

namespace problem2 section
parameters {R : Type _} [comm_ring R]

lemma a : ∀ x y : R, is_nilpotent x → is_nilpotent y → is_nilpotent (x + y) :=
begin
  intros x y hx hy, cases hx with n hx, cases hy with m hy,
  existsi n + m, rw binomial_theorem x y (mul_comm x y),
  rw ← @sum_over_eq_zero _ _ (n+m+1), dsimp [binomial_expansion],
  congr, funext,
  cases k with k hk, simp, by_cases k < n,
  { rw (_ : n + m - k = m + (n - k)), 
    rw [monoid.pow_of_sum_eq_mul, hy], simp,
    rw [nat.add_comm, nat.add_sub_assoc], 
    apply le_of_lt, assumption },
  { rw (_ : x^k = x^(n + (k - n))), 
    rw [monoid.pow_of_sum_eq_mul, hx], simp,
    congr, rw [nat.add_comm, nat.sub_add_cancel],
    apply le_of_not_gt, assumption }
end

lemma b.helper1 : ∀ (x : R) (n : nat), x^n = 0 → (- x)^n = 0 :=
by intros; rw neg_eq_neg_one_mul; rw [power_of_prod, a, mul_zero]

lemma b.helper2 : ∀ (x y : R), x * y = 1 → ∀ (n : nat), x^n * y^n = 1 :=
by intros; rw [← power_of_prod]; rw a; rw power_of_one n

lemma b : ∀ x y : R, is_nilpotent x → is_unit y → is_unit (x + y) :=
begin
  intros x y hx hy, cases hy with y_inv hy, cases hx with n hx,
  cases n with n; simp [(^), mul_n_times] at hx,
  { existsi (0 : R), rw hx, apply mul_zero },
  cases n with n,
  { simp [ mul_n_times] at hx, subst hx,
    rw zero_add, existsi y_inv, assumption },
  rw (_ : (x + y) = -((- 1) - x * y_inv) * y),
  { existsi y_inv * elephant (- 1) (x * y_inv) (nat.succ (nat.succ (n * 2))),
    rw mul_assoc, transitivity -(-1 - x * y_inv) * ((y * y_inv) * elephant (-1) (x * y_inv) (nat.succ (nat.succ (n * 2)))),
    rw mul_assoc, rw [hy, one_mul], 
    { rw [neg_eq_neg_one_mul, mul_assoc],
      rw [← elephant_teacup],
      rw (_ : (x * y_inv) ^ nat.succ (nat.succ (nat.succ (n * 2))) = (x * y_inv) ^ ((n+2) + (n + 1))),
      { rw [monoid.pow_of_sum_eq_mul, power_of_prod], 
        rw (_ : x ^ (n + 2) = mul_n_times x (nat.succ n) * x),
        rw [hx, zero_mul, zero_mul, sub_zero, mul_comm],
        transitivity (-1 : R)^((n+2)*2),
        { dsimp [(^)], congr, dsimp [(*)],
          rw [(_ : nat.add 1 0 = 1), (_ : nat.add n 0 = n), (_ : nat.mul (n+2) 1 = n + 2)],
          rw [(_ : nat.mul n 2 = n + n), (_ : n + 2 = n.succ.succ)], 
          rw ← nat.succ_add, rw ← nat.succ_add, refl,
          any_goals {refl},
          rw ← nat.mul_two, refl,
          transitivity (n+2)*1, refl, rw mul_one },
        { rw mul_comm, rw exp_of_prod, rw (_ : (-1)^2 = (1 : R)),
          apply power_of_one, dsimp [(^), mul_n_times], 
          rw [one_mul], rw problem1.b },
        { refl } },
      congr, rw nat.mul_two, 
      rw [(_ : nat.add n 0 = n), (_ : n + 2 = n.succ.succ)],
      rw [← nat.succ_add, ← nat.succ_add], refl, refl, refl,
      rw mul_comm, } },
  { rw [neg_sub, sub_neg_eq_add, right_distrib],
    rw [one_mul, mul_assoc, mul_comm _ y, hy, mul_one] }
end

end end problem2

-- for parts a and c, see boolean_rings
namespace problem3

lemma b {R} [integral_domain R]
  : (∀ x : R, x*x = x) → (∀ x : R, x = 1 ∨ x = 0) :=
begin
  intros is_bool x,
  rw (_ : x = 1 ↔ 1 + -x = 0),
  apply eq_zero_or_eq_zero_of_mul_eq_zero,
  rw [right_distrib, neg_mul_eq_neg_mul_symm, is_bool],
  rw one_mul, apply add_neg_self,
  constructor; intro h, subst h, apply add_neg_self,
  rw eq_add_of_add_neg_eq h, simp,
end

end problem3

namespace problem4 section

parameters {R : Type _} [ring R]

def a.helper1 (aₙ : sequence R) (b₀ : R) : sequence R
| 0 := b₀
| (nat.succ n) := b₀ * -sum_over
        (λ (j : fin (nat.succ n)),
           have this : n - j.val < nat.succ n := nat.lt_of_le_of_lt (nat.sub_le _ _) (nat.lt_succ_self _),
           aₙ j.val.succ * a.helper1 (n - j.val))

lemma a.helper1.of_zero (aₙ : sequence R) (b₀ : R) : a.helper1 aₙ b₀ 0 = b₀ := rfl
lemma a.helper1.of_succ (aₙ : sequence R) (b₀ : R)
  : ∀ n, a.helper1 aₙ b₀ (nat.succ n)
       = b₀ * -sum_over
          (λ (j : fin (nat.succ n)),
            aₙ j.val.succ * a.helper1 aₙ b₀ (n - j.val)) :=
  λ _, rfl

lemma a : ∀ p : R[[x]], is_unit p ↔ is_unit (p.coefficients 0) :=
begin
  intro p,
  constructor,
  { intro h, cases h with q h, 
    existsi q.coefficients 0,
    have : (p*q).coefficients 0 = power_series.coefficients 1 0,
    { rw h }, dsimp [power_series.coefficients, (∗)] at this,
    dsimp [sum_over] at this, rw zero_add at this, exact this },
  { intro h, cases h with b₀ h,
    existsi (power_series.mk (a.helper1 p.coefficients b₀)),
    apply power_series.eq, intro, dsimp [power_series.coefficients],
    cases n with n,
    { dsimp [(∗), sum_over], rw (a.helper1.of_zero), rw [zero_add, h], refl },
    { dsimp [(∗)], rw sum_over.step_front, simp,
      rw [a.helper1.of_succ, ← mul_assoc, h, one_mul],
      rw add_comm, rw add_neg_self, refl } }
end

end end problem4

section week2



end week2