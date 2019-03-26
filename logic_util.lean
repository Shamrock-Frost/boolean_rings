instance {T} {S : set T} [h : decidable_pred S]
  : decidable_pred (set.compl S) :=
  λ x, decidable.cases_on (h x)
          (λ h, is_true h)
          (λ h, is_false (λ h', h' h))

lemma and.distrib_left (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
iff.intro
  (assume h : P ∧ (Q ∨ R),
   have hp : P := and.left h,
   show (P ∧ Q) ∨ (P ∧ R),
   from h.right.cases_on
          (λ hq, or.inl (and.intro hp hq))
          (λ hr, or.inr (and.intro hp hr)))
  (assume h : (P ∧ Q) ∨ (P ∧ R),
   show P ∧ (Q ∨ R),
   from or.cases_on h
        (λ hpq : P ∧ Q, and.intro hpq.left (or.inl hpq.right))
        (λ hpr : P ∧ R, and.intro hpr.left (or.inr hpr.right)))

lemma and.distrib_right (P Q R : Prop) : (Q ∨ R) ∧ P ↔ (Q ∧ P) ∨ (R ∧ P) :=
by { rw and_comm, rw and.distrib_left,
     rw and_comm P Q, rw and_comm P R, }

lemma or.distrib_left (P Q R : Prop) : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
iff.intro
  (assume h : P ∨ (Q ∧ R),
   show (P ∨ Q) ∧ (P ∨ R),
   from h.cases_on
          (λ hp, and.intro (or.inl hp) (or.inl hp))
          (λ hqr, and.intro (or.inr hqr.left) (or.inr hqr.right)))
  (by {
    intro h,
    cases h,
    cases h_left,
    { exact or.inl h_left },
    { cases h_right,
      { exact or.inl h_right },
      { apply or.inr, constructor; assumption } } })

lemma or.distrib_right (P Q R : Prop) : (Q ∧ R) ∨ P ↔ (Q ∨ P) ∧ (R ∨ P) :=
by { rw or_comm, rw or.distrib_left,
     rw or_comm P Q, rw or_comm P R }

lemma not_or_iff_and_not (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
begin
  constructor; intro h,
  { constructor; intro h'; apply h,
    { apply or.inl, assumption }, { apply or.inr, assumption } },
  { intro h', cases h, cases h',
    { exact h_left h' }, { exact h_right h' } }
end

lemma and_not_and (p q : Prop) : p ∧ ¬(p ∧ q) ↔ p ∧ ¬q :=
begin
  constructor; intro h; cases h,
  { constructor, assumption,
    intro hp, apply h_right, 
    constructor; assumption },
  { constructor, assumption,
    intro hpq, apply h_right, cases hpq, assumption }
end

lemma subset_of_empty_iff_empty {T} {A : set T}  : A ⊆ ∅ ↔ A = ∅ :=
by { simp [(⊆), set.subset], constructor,
     { intro h, funext, apply propext,
      constructor, { apply h }, { intro h, cases h } },
     { intro h, rw h, intro, exact id } }

lemma inter_subset_l {T} (A B : set T) : A ∩ B ⊆ A := λ _, and.left
lemma inter_subset_r {T} (A B : set T) : A ∩ B ⊆ B := λ _, and.right
lemma subset_union_l {T} (A B : set T) : A ⊆ A ∪ B := λ _, or.inl
lemma subset_union_r {T} (A B : set T) : B ⊆ A ∪ B := λ _, or.inr

def fun.im {A B : Type _} (f : A → B) :=
  { b : B | ∃ a : A, f a = b }

@[reducible]
def disjoint {T} (A B : set T) := A ∩ B = ∅

lemma mk_disjoint {T} (A B : set T)
  : (∀ x : T, ¬ (A x ∧ B x)) → disjoint A B :=
by { intro h, dunfold disjoint, rw ← subset_of_empty_iff_empty, exact h }

lemma elim_disjoint {T} {A B : set T}
  : disjoint A B → ∀ x : T, A x → B x → false :=
by { dunfold disjoint, intros h x ha hb,
     refine (_ : (∅ : set T) x), rw ← h, 
     constructor; assumption }

lemma disjoint_compl {T} (A : set T) : disjoint A (-A) :=
by { apply mk_disjoint, intros x h, exact h.right h.left  }

lemma disjoint_implies_disjoint_subset {T} {A B A' : set T}
  : A' ⊆ A → disjoint A B → disjoint A' B :=
by { intros, apply mk_disjoint, intros x h,
     apply elim_disjoint a_1 x (a h.left) h.right }

lemma inter_comm {T} (A B : set T) : A ∩ B = B ∩ A :=
begin
  funext, apply propext,
  rw (_ : (A ∩ B) a ↔ A a ∧ B a),
  rw (_ : (B ∩ A) a ↔ B a ∧ A a),
  rw and_comm,
  all_goals {refl}
end

lemma disjoint_symm {T} (A B : set T) : disjoint A B ↔ disjoint B A :=
by { dunfold disjoint, rw inter_comm }

lemma union_comm {T} (A B : set T) : A ∪ B = B ∪ A :=
begin
  funext, apply propext,
  rw (_ : (A ∪ B) a ↔ A a ∨ B a),
  rw (_ : (B ∪ A) a ↔ B a ∨ A a),
  rw or_comm,
  all_goals {refl}
end

lemma inter_assoc {T} (A B C : set T) : (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
begin
  funext, apply propext,
  rw (_ : ((A ∩ B) ∩ C) a ↔ (A a ∧ B a) ∧ C a),
  rw (_ : (A ∩ (B ∩ C)) a ↔ A a ∧ (B a ∧ C a)),
  rw and_assoc,
  all_goals {refl}
end

lemma union_assoc {T} (A B C : set T) : (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
begin
  funext, apply propext,
  rw (_ : ((A ∪ B) ∪ C) a ↔ (A a ∨ B a) ∨ C a),
  rw (_ : (A ∪ (B ∪ C)) a ↔ A a ∨ (B a ∨ C a)),
  rw or_assoc,
  all_goals {refl}
end

lemma compl_union {T} (A B : set T) : -(A ∪ B) = -A ∩ -B :=
begin
  funext, apply propext,
  rw (_ : (-(A ∪ B)) a ↔ ¬ (A a ∨ B a)),
  rw (_ : (- A ∩ - B) a ↔ ¬ (A a) ∧ ¬ (B a)),
  rw not_or_iff_and_not,
  all_goals {refl}
end

lemma compl_inter {T} (A B : set T) 
  [decidable_pred A] [decidable_pred B]
  : -(A ∩ B) = -A ∪ -B :=
begin
  funext, apply propext,
  rw (_ : (-(A ∩ B)) a ↔ ¬ (A a ∧ B a)),
  rw (_ : (- A ∪ - B) a ↔ ¬ (A a) ∨ ¬ (B a)),
  rw decidable.not_and_iff_or_not,
  all_goals {refl}
end

lemma union_empty {T} (A : set T) : A ∪ ∅ = A :=
begin
  funext, apply propext,
  rw (_ : (A ∪ ∅) a ↔ A a ∨ false),
  rw or_false,
  refl
end

lemma inter_univ {T} (A : set T) : A ∩ set.univ = A :=
begin
  funext, apply propext,
  rw (_ : (A ∩ set.univ) a ↔ A a ∧ true),
  rw and_true,
  refl
end

lemma inter_empty {T} (A : set T) : A ∩ ∅ = ∅ :=
begin
  funext, apply propext,
  rw (_ : (A ∩ ∅) a ↔ A a ∧ false),
  rw and_false, refl, refl,
end

lemma union_self {T} (A : set T) : A ∪ A = A :=
begin
  funext, apply propext, rw (_ : (A ∪ A) a ↔ A a ∨ A a), 
  rw or_self, refl
end

lemma inter_self {T} (A : set T) : A ∩ A = A :=
begin
  funext, apply propext, rw (_ : (A ∩ A) a ↔ A a ∧ A a), 
  rw and_self, refl
end

lemma elem_singleton {T} (x : T) : {x} = { y : T | y = x } :=
by { rw (_ : {x} = {y : T | y = x} ∪ ∅), apply union_empty, refl }

lemma compl_compl {T} (A : set T)
  [decidable_pred A]
  : - (- A) = A :=
begin
  funext, apply propext,
  rw (_ : (- (- A)) a = ¬ (¬ (A a))),
  rw decidable.not_not_iff,
  refl
end

lemma inter.distrib_left {T} (A B C : set T) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  funext, apply propext,
  rw (_ : (A ∩ (B ∪ C)) a ↔ A a ∧ (B a ∨ C a)),
  rw (_ : ((A ∩ B) ∪ (A ∩ C)) a ↔ (A a ∧ B a) ∨ (A a ∧ C a)),
  { rw and.distrib_left },
  all_goals {refl}
end

lemma inter.distrib_right {T} (A B C : set T) : (B ∪ C) ∩ A = (B ∩ A) ∪ (C ∩ A) :=
by { rw inter_comm, rw inter.distrib_left,
     rw inter_comm A B, rw inter_comm A C }

lemma union.distrib_left {T} (A B C : set T) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
begin
  funext, apply propext,
  rw (_ : (A ∪ (B ∩ C)) a ↔ A a ∨ (B a ∧ C a)),
  rw (_ : ((A ∪ B) ∩ (A ∪ C)) a ↔ (A a ∨ B a) ∧ (A a ∨ C a)),
  { rw or.distrib_left },
  all_goals {refl}
end

lemma union.distrib_right {T} (A B C : set T) : (B ∩ C) ∪ A = (B ∪ A) ∩ (C ∪ A) :=
by { rw union_comm, rw union.distrib_left,
     rw union_comm A B, rw union_comm A C }

lemma set.FOIL1 {T} (A B C D : set T)
  : (A ∪ B) ∩ (C ∪ D) = (A ∩ C) ∪ (B ∩ C) ∪ (A ∩ D) ∪ (B ∩ D) :=
begin
  rw inter.distrib_left,
  rw inter.distrib_right,
  rw inter.distrib_right,
  repeat { rw union_assoc },
end

lemma set.FOIL2 {T} (A B C D : set T)
  : (A ∩ B) ∪ (C ∩ D) = (A ∪ C) ∩ (B ∪ C) ∩ (A ∪ D) ∩ (B ∪ D) :=
begin
  rw union.distrib_left,
  rw union.distrib_right,
  rw union.distrib_right,
  repeat { rw inter_assoc },
end

def set_minus {T} (A B : set T) : set T := { x ∈ A | x ∉ B }
infix `∖`:80 := set_minus

lemma minus_is_subset {T} (A B : set T) : A ∖ B ⊆ A := λ _ h, h.left

lemma minus_eq_inter_compl {T} (A B : set T) : A ∖ B = A ∩ (-B) :=
begin
  funext, apply propext,
  rw (_ : (A ∖ B) a ↔ A a ∧ ¬ (B a)),
  rw (_ : (A ∩ -B) a ↔ A a ∧ ¬ (B a)),
  refl, refl,
end

lemma minus_disj {T} (A B : set T) : disjoint (A ∖ B) B :=
begin
  rw [minus_eq_inter_compl],
  apply disjoint_implies_disjoint_subset,
  apply inter_subset_r, rw disjoint_symm, apply disjoint_compl
end

lemma union_minus {T} (A B C : set T) : (A ∪ B) ∖ C = (A ∖ C) ∪ (B ∖ C) :=
begin
  funext, apply propext,
  rw (_ : (((A ∪ B)∖C) a ↔ (A a ∨ B a) ∧ ¬ (C a))),
  rw (_ : ((A∖C) ∪ (B∖C)) a ↔ (A a ∧ ¬(C a)) ∨ (B a ∧ ¬(C a))),
  apply and.distrib_right,
  all_goals {refl}
end

lemma minus_subset_union_subset {T} {A A' : set T}
  [decidable_pred A]
  : A ⊆ A' → (A' ∖ A) ∪ A = A' :=
begin
  intros hsub, funext, apply propext, constructor,
  { intro h, cases h,
    { exact h.left },
    { apply hsub, assumption } },
  { intro h, by_cases h' : A a,
    { exact or.inr h' },
    { exact or.inl ⟨h, h'⟩ } }
end

lemma minus_inter {T} (A B C : set T)
  [decidable_pred B] [decidable_pred C]
  : A ∖ (B ∩ C) = (A ∖ B) ∪ (A ∖ C) :=
begin
  funext, apply propext,
  rw (_ : (A∖(B ∩ C)) a ↔ A a ∧ ¬ (B a ∧ C a)),
  rw (_ : ((A∖B) ∪ (A∖C)) a ↔ (A a ∧ ¬ (B a)) ∨ (A a ∧ ¬ (C a))),
  { rw decidable.not_and_iff_or_not,
    apply and.distrib_left },
  all_goals {refl}
end

lemma minus_union {T} (A B C : set T)
  : A ∖ (B ∪ C) = (A ∖ B) ∩ (A ∖ C) :=
begin
  funext, apply propext,
  rw (_ : (A∖(B ∪ C)) a ↔ A a ∧ ¬ (B a ∨ C a)),
  rw (_ : ((A∖B) ∩ (A∖C)) a ↔ (A a ∧ ¬ (B a)) ∧ (A a ∧ ¬ (C a))),
  rw [not_or_iff_and_not
     , and_assoc
     , ← and_assoc (¬ (B a)) (A a)
     , and_comm (¬ (B a)) (A a)
     , and_assoc
     , ← and_assoc (A a) (A a)
     , and_self
     ],
  all_goals {refl}
end

lemma minus_eq_minus_inter {T} (A B : set T) : A ∖ B = A ∖ (A ∩ B) :=
begin
  funext, apply propext,
  rw (_ : (A∖B) a ↔ A a ∧ ¬ B a),
  rw (_ : (A∖(A ∩ B)) a ↔ A a ∧ ¬ (A a ∧ B a)),
  { constructor;
    intro h; cases h;
    apply and.intro h_left; intro h'; apply h_right,
    { exact h'.right },
    { exact and.intro h_left h' } },
  all_goals {refl}
end

lemma minus_self {T} (A : set T) : A ∖ A = ∅ :=
begin
  funext, apply propext, constructor;
  intro h; exfalso,
  { have : A a ∧ ¬ (A a) := h,
    exact this.right this.left },
  { exact h }
end

lemma minus_empty {T} (A : set T) : A∖∅ = A :=
begin
  funext, apply propext, 
  rw (_ : (A ∖ ∅) a ↔ A a ∧ ¬ false),
  { rw [not_false_iff, and_true] }, refl
end

lemma minus_minus_eq_minus_union {T} (A B C : set T) : (A ∖ B) ∖ C = A ∖ (B ∪ C) :=
begin
  funext, apply propext,
  rw (_ : (A∖B∖C) a ↔ (A a ∧ ¬ (B a)) ∧ ¬ (C a)),
  rw (_ : (A ∖ (B ∪ C)) a ↔ A a ∧ ¬ (B a ∨ C a)),
  { rw and_assoc, rw not_or_iff_and_not },
  all_goals {refl}
end

lemma minus_of_minus {T} (A B C : set T)
  [decidable_pred B] [decidable_pred C]
  : A ∖ (B ∖ C) = (A ∖ B) ∪ (A ∩ C) :=
begin
  rw minus_eq_inter_compl A B,
  rw ← inter.distrib_left,
  rw minus_eq_inter_compl A,
  rw minus_eq_inter_compl B,
  rw compl_inter B (-C),
  rw compl_compl
end

def symm_diff {T} (A B : set T) : set T := (A ∪ B) ∖ (A ∩ B)
infix `Δ`:60 := symm_diff

lemma symm_diff_def2 {T} (A B : set T) : A Δ B = (A ∖ B) ∪ (B ∖ A) := by {
  dsimp [(Δ)],
  rw union_minus,
  apply congr,
  { apply congr_arg, rw ← minus_eq_minus_inter },
  { rw inter_comm, rw ← minus_eq_minus_inter }
}

lemma symm_diff_comm {T} (A B : set T) : A Δ B = B Δ A :=
  by dsimp [(Δ)]; rw [inter_comm, union_comm]

lemma minus_inter_inter_eq_empty {T} (A B : set T) : A∖B ∩ (A ∩ B) = ∅ :=
begin
  rw minus_eq_inter_compl,
  rw inter_assoc,
  rw ← inter_assoc (- B),
  rw inter_comm (-B),
  rw inter_assoc A (-B),
  rw inter_comm (-B),
  rw ← minus_eq_inter_compl,
  rw minus_self,
  rw inter_empty, rw inter_empty
end

lemma minus_of_symm_diff {T} (A B C : set T)
  [decidable_pred A] [decidable_pred B] [decidable_pred C]
  : C ∖ (A Δ B) = ((C ∖ A) ∩ (C ∖ B)) ∪ (C ∩ A ∩ B) :=
begin
  rw symm_diff_def2, rw ← minus_union,
  rw minus_union,
  rw [minus_of_minus, minus_of_minus],
  rw set.FOIL1,
  rw (_ : C ∩ B ∩ C∖B = ∅),
  rw (_ : C∖A ∩ (C ∩ A) = ∅),
  rw union_empty, rw union_empty,
  rw minus_union,
  have : C ∩ B ∩ (C ∩ A) = C ∩ A ∩ B,
  { rw ← inter_assoc,
    rw inter_comm C B,
    rw inter_assoc B C C,
    rw inter_self,
    rw inter_assoc,
    rw inter_comm },
  rw this,
  { apply minus_inter_inter_eq_empty },
  { rw inter_comm, apply minus_inter_inter_eq_empty }
end

lemma symm_diff_assoc {T} (A B C : set T) 
  [decidable_pred A] [decidable_pred B] [decidable_pred C]
  : (A Δ B) Δ C = A Δ (B Δ C) :=
begin
  rw symm_diff_def2,
  rw minus_of_symm_diff,
  rw symm_diff_def2,
  rw symm_diff_def2,
  rw minus_of_symm_diff,
  rw symm_diff_def2,

  rw union_minus,
  rw minus_minus_eq_minus_union,
  rw minus_union,
  rw minus_minus_eq_minus_union,
  rw minus_union,

  rw union_minus,
  rw minus_minus_eq_minus_union,
  rw minus_union,
  rw minus_minus_eq_minus_union,
  rw minus_union,

  suffices : B∖A ∩ B∖C ∪ (C∖A ∩ C∖B ∪ C ∩ A ∩ B)
           = A ∩ B ∩ C ∪ (B∖C ∩ B∖A ∪ C∖B ∩ C∖A),
  { rw union_assoc, rw this, rw ← union_assoc },

  rw ← union_assoc,
  rw ← union_assoc,
  rw union_comm,
  rw ← union_assoc,
  rw (_ : C ∩ A ∩ B = A ∩ B ∩ C),
  rw (_ : B∖A ∩ B∖C = B∖C ∩ B∖A),
  rw (_ : C∖A ∩ C∖B = C∖B ∩ C∖A),
  rw inter_comm, rw inter_comm,
  rw inter_assoc, rw inter_comm
end

lemma empty_symm_diff {T} (A : set T) : ∅ Δ A = A :=
by { intros, simp [(Δ)],
     rw [union_comm, inter_comm],
     rw [union_empty, inter_empty, minus_empty] } 

lemma symm_diff_self {T} (A : set T) : A Δ A = ∅ :=
by { dsimp [(Δ)], rw union_self, rw inter_self, apply minus_self }

lemma left_distrib_inter_symm_diff {T} (A B C : set T)
  : A ∩ (B Δ C) = (A ∩ B) Δ (A ∩ C) :=
begin
  rw symm_diff_def2, rw symm_diff_def2,
  rw inter.distrib_left,
  have : ∀ A' B' C' : set T, A' ∩ B'∖C' = (A' ∩ B')∖(A' ∩ C'),
  { intros, rw minus_eq_inter_compl,
    rw minus_eq_inter_compl,
    suffices : A' ∩ -C' = A' ∩ -(A' ∩ C'),
    { rw ← inter_assoc,
      rw inter_comm,
      rw ← inter_assoc,
      rw inter_comm (-C'),
      rw this,
      rw inter_assoc,
      rw inter_assoc,
      rw inter_comm B' },
    { funext, apply propext,
      rw (_ : (A' ∩ -C') a ↔ A' a ∧ ¬ (C' a)),
      rw (_ : (A' ∩ -(A' ∩ C')) a ↔ A' a ∧ ¬ (A' a ∧ C' a)),
      { rw and_not_and }, 
      all_goals {refl} } },
  rw ← this,
  rw ← this
end

lemma union_decomp_symm {T} (A B : set T)
  [decidable_pred A] [decidable_pred B]
 : A ∪ B = (A Δ B) ∪ (A ∩ B) :=
begin
  dsimp [(Δ)], symmetry,
  apply @minus_subset_union_subset _ _ _ _,
  exact λ _, or.inl ∘ and.left,
  intro x, 
  by_cases h : A x; by_cases h' : B x,
  { apply decidable.is_true,
    constructor; assumption },
  { apply decidable.is_false,
    intro h'', cases h'',
    apply h', assumption },
  all_goals 
  { apply decidable.is_false,
    intro h'', cases h'',
    apply h, assumption }
end

lemma union_decomp_l {T} (A B : set T)
  [decidable_pred A]
 : A ∪ B = A ∪ (B ∖ A) :=
begin
  funext x, apply propext,
  constructor; intro h, 
  { by_cases h' : A x,
    { exact or.inl h' },
    { cases h, { exfalso, apply h', assumption },
      apply or.inr, constructor; assumption } },
  { cases h, exact or.inl h, exact or.inr (minus_is_subset _ _ h) }
end

lemma union_decomp_r {T} (A B : set T)
  [decidable_pred B]
 : A ∪ B = (A ∖ B) ∪ B :=
begin
  transitivity B ∪ A, apply union_comm,
  transitivity B ∪ (A ∖ B), apply union_decomp_l,
  apply union_comm
end

lemma symm_diff_disj_inter {T} (A B : set T)
  : disjoint (A Δ B) (A ∩ B) := minus_disj (A ∪ B) (A ∩ B)

lemma decomp {T} (A B : set T) [decidable_pred B]
  : A = (A ∖ B) ∪ (A ∩ B) :=
begin
  funext, apply propext,
  constructor,
  { intro h, by_cases h' : B x,
    { apply or.inr, constructor; assumption },
    { apply or.inl, constructor; assumption } },
  { intro h, cases h; cases h; assumption }
end

def subset_of_subtype_to_subset {A : Type _} {P : A → Prop}
  : set (subtype P) → set A :=
  λ S, { a : A | ∃ h : P a, S ⟨a, h⟩ } 