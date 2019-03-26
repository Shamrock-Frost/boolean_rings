def fun.im {A B : Type _} (f : A → B) := { b : B | ∃ a, f a = b }
def set.finite {T : Type _} (S : set T) := ∃ n (f : fin n → T), function.injective f ∧ (S = fun.im f)

def LEM := ∀ P : Prop, P ∨ ¬ P
def finite_subsets := ∀ {T : Type} {S S' : set T}, S ⊆ S' → set.finite S' → set.finite S

lemma zero_only_elem_fin_1 : ∀ x : fin 1, x = ⟨0,nat.zero_lt_one⟩
| ⟨0,   h⟩ := rfl
| ⟨n+1, h⟩ := 
  have 1 + n < 1 + 0,
  from nat.add_comm n 1 ▸ h,
  have n < 0,
  from nat.lt_of_add_lt_add_left this,
  absurd this (nat.not_lt_zero n)

theorem finite_subsets_are_finite_imp_LEM (fin_sub : finite_subsets) : LEM :=
λ P,
  let f1 : fin 1 → nat := λ _, 0 in
  have f1_i : ∀ x y, f1 x = f1 y → x = y,
  from λ x y _, eq.trans (zero_only_elem_fin_1 x)
              $ eq.symm $ zero_only_elem_fin_1 y,
  have f1_s.helper : ∀ x, (x = 0) ↔ (∃ k, f1 k = x),
  from λ x, iff.intro (λ h, eq.symm h ▸ ⟨⟨0, zero_lt_one⟩, rfl⟩)
                      (λ h, exists.elim h (λ _ h', eq.symm h')),
  have f1_s : { y : nat | y = 0 } = { b : ℕ | ∃ k, f1 k = b },
  from funext (λ x, propext $ f1_s.helper x),
  have h1 : set.finite { y : nat | y = 0 },
  from ⟨1, f1, f1_i, f1_s⟩,
  have h2 : {y : nat | y = 0 ∧ P} ⊆ { y : nat | y = 0 },
  from λ x h, h.left,
  have h3 : set.finite {y : nat | y = 0 ∧ P },
  from fin_sub h2 h1,
  have im_empty : ∀ (f : fin 0 → nat) x, fun.im f x → false,
  from λ f x h, exists.elim h $ λ a, fin.elim0 a,
  have neg_case : (∃ (f : fin 0 → nat), function.injective f ∧ {y : nat | y = 0 ∧ P} = fun.im f) → ¬P,
  from λ e, exists.elim e (λ f ⟨_, h⟩ hp, im_empty f 0 $ h ▸ ⟨rfl, hp⟩),
  have pos_case : ∀ k, 0 < k → (∃ (f : fin k → nat), function.injective f ∧ {y : nat | y = 0 ∧ P} = fun.im f) → P,
  from λ k hk e, exists.elim e $ λ f ⟨_, h⟩,
          have h' : fun.im f (f ⟨0, hk⟩),
          from ⟨⟨0, hk⟩, rfl⟩,
          have h'' : { y : nat | y = 0 ∧ P } (f ⟨0, hk⟩), 
          from eq.symm h ▸ h',
          and.right h'',
  exists.elim h3 $
    λ k, match nat.decidable_eq 0 k with
         | is_true h := h ▸ λ x, or.inr $ neg_case x
         | is_false h :=  
          have k_pos : 0 < k,
          from nat.pos_of_ne_zero (ne.symm h),
          λ x, or.inl $ pos_case k k_pos x
         end