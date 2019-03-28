import .finite

inductive {u} set.acc {α : Type u} (r : α → α → Prop) (S : set α)
  : α → Prop
| intro (x : α) (h : ∀ y ∈ S, r y x → set.acc y) : set.acc x

lemma {u} set_acc_of_set_acc_minus {α : Type u} (r : α → α → Prop) (S S' : set α)
  (r_trans : ∀ x y z, r x y → r y z → r x z)
  : ∀ y ∈ S, (∀ y' ∈ S', ¬ r y' y) → (S ∖ S').acc r y → S.acc r y :=
begin
  intros y hy h hacc,
  induction hacc with y h ih, constructor,
  intros y' hy' hr,
  have : y' ∉ S' := λ h', h y' h' hr,
  apply ih, constructor; assumption,
  assumption, assumption,
  intros y'' h'' h''', apply h y'' h'', 
  apply r_trans; assumption,
end

lemma partial_order.finite_well_founded
  {X : Type _} [partial_order X] (is_fin : finite X)
  : well_founded (@partial_order.lt X _) :=
begin
  constructor,
  suffices : ∀ x : X, x ∈ @set.univ X → set.acc partial_order.lt (@set.univ X) x,
  { intro x, apply @set.acc.rec_on X (<) set.univ (acc (<)),
    { apply this, constructor },
    { clear x, intros, constructor,
       intros y hy, exact ih y true.intro hy } },
  have : set.finite (@set.univ X),
  { cases is_fin with size h, existsi size,
    cases h with f h, cases h with f_i f_s,
    existsi f, constructor, assumption,
    funext, apply propext, transitivity true,
    refl, rw true_iff, exact f_s a },
  cases this with size h,
  generalize q : set.univ = S, rw q at h, clear q,
  revert S h, induction size with n ih;
  intros; cases h with f h; cases h with f_i f_s,
  { rw f_s at a, exfalso, cases a, exact a_w.elim0 },
  constructor, intros,
  have : y ∈ { y ∈ S | y ≠ x } := ⟨H, ne_of_lt a_1⟩,
  cases ih { y ∈ S | y ≠ x } _ y this,
  { apply set_acc_of_set_acc_minus (<) S {x} (@lt_trans X _) _ H;
    rw elem_singleton,
    { intros y' h', rw (_ : y' = x),
      apply lt_asymm, assumption, assumption },
    { constructor, intros y' h' hlt, apply h; assumption } },
  { rw f_s at a, cases a,
    existsi fin.fun_omit a_w.val f, constructor,
    apply omit_inj_if_fun_inj _ _ f_i,
    rw [im_omit _ _ _ f_i, elem_singleton, f_s], 
    rw a_h, refl }
end

theorem partial_order.induction {X : Type _} [partial_order X]
  (P : X → Prop) (is_fin : finite X)
  (ih : ∀ x , (∀ y, y < x → P y) → P x)
  : ∀ x, P x :=
  λ x, well_founded.induction (partial_order.finite_well_founded is_fin) x ih

def minimal {X : Type _} [partial_order X] (P : X → Prop)
  := λ x : X, P x ∧ ∀ y, y < x → ¬ P y

theorem partial_order.ex_min {X : Type _} [partial_order X]
  (is_fin : finite X) (P : X → Prop)
  : ∀ x, P x → ∃ y, minimal P y ∧ y ≤ x :=
begin
  apply partial_order.induction (λ x, P x → ∃ y, minimal P y ∧ y ≤ x) is_fin,
  intros x ih hp,
  cases classical.em (minimal P x),
  { existsi x, constructor, assumption, refl },
  { dsimp [minimal] at h, 
    rw @decidable.not_and_iff_or_not _ _
      (classical.prop_decidable _) (classical.prop_decidable _) at h,
    have h := or.resolve_left h,
    rw ← classical.dne (P x) at h, specialize h hp,
    cases classical.exists_of_not_forall h with y hy,
    simp at hy,
    rw classical.implies_iff_or at hy,
    rw not_or_iff_and_not at hy,
    rw ← classical.dne (y < x) at hy,
    rw ← classical.dne (P y) at hy,
    cases ih y hy.left hy.right,
    cases h_1, existsi w, constructor,
    assumption, transitivity, assumption,
    apply le_of_lt, exact hy.left }
end