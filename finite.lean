import .logic_util .nat_util

def fin.glue {A} {n m} (f : fin n → A) (g : fin m → A) : fin (n + m) → A :=
λ k, if h : k.val < n
     then f ⟨k.val, h⟩
     else g ⟨k.val - n, sub_lt_if_ge n m k.val (ge_if_not_lt h) k.is_lt⟩

lemma both_inj_and_im_disj_implies_glue_inj {A} {n m}
  : ∀ (f : fin n → A) (g : fin m → A),
    function.injective f
    → function.injective g
    → disjoint (fun.im f) (fun.im g)
    → function.injective (fin.glue f g) :=
begin
  intros f g f_i g_i h_disj,
  intros x y hxy,
  simp [fin.glue] at hxy,
  by_cases hx : x.val < n,
  { by_cases hy : y.val < n,
    { apply fin.eq_of_veq, rw [dif_pos hx, dif_pos hy] at hxy,
      refine (_ : (fin.mk x.val hx).val = (fin.mk y.val hy).val),
      apply fin.veq_of_eq, apply f_i, assumption },
    { exfalso, rw [dif_pos hx, dif_neg hy] at hxy, 
      refine (_ : (∅ : set A) (f ⟨x.val, hx⟩)),
      dsimp [disjoint] at h_disj, rw ← h_disj,
      constructor,
      existsi _, refl,
      rw hxy, existsi _, refl } },
  { by_cases hy : y.val < n,
    { exfalso, rw [dif_neg hx, dif_pos hy] at hxy, 
      refine (_ : (∅ : set A) (f ⟨y.val, hy⟩)),
      dsimp [disjoint] at h_disj, rw ← h_disj,
      constructor,
      existsi _, refl,
      rw ← hxy, existsi _, refl },
    { apply fin.eq_of_veq, rw [dif_neg hx, dif_neg hy] at hxy,
      have := fin.veq_of_eq (g_i hxy), simp at this,
      have hx : n ≤ x.val := ge_if_not_lt hx,
      have hy : n ≤ y.val := ge_if_not_lt hy,
      rw [← nat.add_sub_of_le hx, ← nat.add_sub_of_le hy, this] } }
end

lemma im_glue_eq_union_ims {A} {n m}
  : ∀ (f : fin n → A) (g : fin m → A),
    fun.im (fin.glue f g) = fun.im f ∪ fun.im g :=
begin
  intros f g, funext, apply propext,
  constructor; intro h; cases h,
  { by_cases h_w.val < n,
    { apply or.inl, existsi fin.mk h_w.val h,
      simp [fin.glue] at h_h, rw [← h_h, dif_pos h] },
    { apply or.inr,
      existsi fin.mk (h_w.val - n) (sub_lt_if_ge n m h_w.val (ge_if_not_lt h) h_w.is_lt),
      simp [fin.glue] at h_h, rw [dif_neg] at h_h, assumption } },
  { cases h, existsi fin.mk h_w.val (nat.lt_of_lt_of_le h_w.is_lt (nat.le_add_right _ _)),
    simp [fin.glue], rw [dif_pos h_w.is_lt],
    rw ← h_h, congr, apply fin.eq_of_veq, refl },
  { cases h, existsi fin.mk (n + h_w.val) (nat.add_lt_add_left h_w.is_lt n),
    have h1 : ¬ (n + h_w.val < n),
    { have := nat.le_add_right n h_w.val,
      intro, apply nat.lt_irrefl (n + h_w.val),
      apply nat.lt_of_lt_of_le; assumption },
    simp [fin.glue], rw [dif_neg h1],
    rw ← h_h, congr, apply fin.eq_of_veq, simp,
    apply nat.add_sub_cancel_left }
end

def fin.restrict {A} {n} (f : fin (nat.succ n) → A) : fin n → A :=
λ k, f ⟨k.val, nat.lt_trans k.is_lt $ nat.lt_succ_self n⟩

lemma fin.restrict_glue_comm {A} {n m : ℕ}
  : ∀ (f : fin n → A) (g  : fin (nat.succ m) → A),
    fin.restrict (fin.glue f g) = fin.glue f (fin.restrict g) :=
  by intros; refl

def fin.fun_omit {A : Type _} {n} (k : nat) (f : fin (nat.succ n) → A) : fin n → A :=
λ m, if hmk : m.val < k
     then f ⟨m.val, nat.lt_trans m.is_lt $ nat.lt_succ_self n⟩
     else f ⟨m.val+1, nat.add_lt_add_right m.is_lt 1⟩

lemma restrict_is_omit_n {T n}
  : ∀ (f : fin (nat.succ n) → T), fin.restrict f = fin.fun_omit n f :=
begin
  intros, funext,
  simp [fin.restrict, fin.fun_omit],
  rw dif_pos, exact k.is_lt
end

lemma omit_inj_if_fun_inj {A : Type _} {n} (k : nat) (f : fin (nat.succ n) → A)
  : function.injective f → function.injective (fin.fun_omit k f) :=
begin
  intros f_inj x y hxy,
  by_cases h : x.val < k; by_cases h' : y.val < k,
  { dsimp [fin.fun_omit] at hxy,
    rw [dif_pos h, dif_pos h'] at hxy,
    apply fin.eq_of_veq,
    have := f_inj hxy, 
    apply fin.veq_of_eq this },
  { exfalso, dsimp [fin.fun_omit] at hxy,
    rw [dif_pos h, dif_neg h'] at hxy,
    have : x.val = y.val + 1,
    { have := f_inj hxy, apply fin.veq_of_eq this },
    rw this at h, apply h',
    apply nat.lt_trans _ h,
    apply nat.lt_succ_self },
  { exfalso, dsimp [fin.fun_omit] at hxy,
    rw [dif_neg h, dif_pos h'] at hxy,
    have : x.val + 1 = y.val,
    { have := f_inj hxy, apply fin.veq_of_eq this },
    rw ← this at h', apply h,
    apply nat.lt_trans _ h',
    apply nat.lt_succ_self },
  { dsimp [fin.fun_omit] at hxy,
    rw [dif_neg h, dif_neg h'] at hxy,
    apply fin.eq_of_veq,
    apply nat.succ_inj,
    exact fin.veq_of_eq (f_inj hxy) }
end


lemma restrict_inj_if_fun_inj {A : Type _} {n} (f : fin (nat.succ n) → A)
  : function.injective f → function.injective (fin.restrict f) :=
  eq.substr (restrict_is_omit_n f) (omit_inj_if_fun_inj n f)

lemma im_omit {T : Type _}
  : ∀ n (f : fin (nat.succ n) → T) (k : fin (nat.succ n)),
    function.injective f →
    fun.im (fin.fun_omit k.val f) = fun.im f ∖ {f k} :=
begin
  intros n f k f_i,
  funext, apply propext, constructor; intro h,
  { cases h with m h,
    have : (f ⟨m.val, nat.lt_trans m.is_lt (nat.lt_succ_self n)⟩ = b)
         ∨ (f ⟨m.val + 1, nat.succ_lt_succ m.is_lt⟩ = b),
    { dsimp [fin.fun_omit] at h,
      by_cases h' : m.val < k.val,
      { rw dif_pos h' at h, apply or.inl, assumption },
      { rw dif_neg h' at h, apply or.inr, assumption } },
    cases this,
    { constructor,
      { existsi _, exact this },
      { rw elem_singleton, intro h', cases h',
        rw eq.symm (fin.veq_of_eq (f_i this)) at h, simp at h,
        rw ← this at h,
        dsimp [fin.fun_omit] at h,
        rw dif_neg (nat.lt_irrefl m.val) at h,
        apply nat.succ_ne_self m.val,
        exact fin.veq_of_eq (f_i h) } },
    { constructor,
      { existsi _, exact this },
      { rw elem_singleton, intro h', cases h',
        rw eq.symm (fin.veq_of_eq (f_i this)) at h, simp at h,
        rw ← this at h,
        dsimp [fin.fun_omit] at h,
        rw dif_pos (nat.lt_succ_self m.val) at h,
        apply nat.succ_ne_self m.val, symmetry,
        exact fin.veq_of_eq (f_i h) } } },
  { cases h, cases h_left with m hm,
    cases (nat.lt_trichotomy m.val k.val),
    { existsi fin.mk m.val (nat.lt_of_lt_of_le h $ nat.le_of_lt_succ k.is_lt),
      dsimp [fin.fun_omit], rw dif_pos h, 
      rw ← hm, congr, apply fin.eq_of_veq, refl },
    { have := or.resolve_left h _,
      { destruct m.val,
        { intro h, rw h at this, cases this },
        { intros m' hm',
          have m'_is_lt : m' < n,
          { apply nat.lt_of_lt_of_le,
            apply nat.lt_succ_self,
            rw ← hm', apply nat.le_of_lt_succ,
            exact m.is_lt },
          existsi fin.mk m' m'_is_lt,
          { dsimp [fin.fun_omit],
            rw dif_neg _, rw ← hm,
            congr, apply fin.eq_of_veq, 
            exact eq.symm hm',
            intro h, apply nat.not_self_lt_lt_succ_self,
            exact h, rw nat.add_one, rw ← hm', exact this },  } },
      { intro hmk, apply h_right,
        rw elem_singleton,
        rw [fin.eq_of_veq (eq.symm hmk), hm],
        constructor } } }
end

lemma im_restrict {T : Type _}
  : ∀ n (f : fin (nat.succ n) → T),
    function.injective f →
    fun.im (fin.restrict f) = fun.im f ∖ {f ⟨n,nat.lt_succ_self n⟩} :=
  by { intros, rw restrict_is_omit_n,
       rw (_ : fin.fun_omit n f = fin.fun_omit (fin.mk n (nat.lt_succ_self n)).val f),
       apply im_omit, assumption, refl }

def has_size (T : Type _) (n) := ∃ (f : fin n → T), function.bijective f
def finite (T : Type _) := ∃ n, has_size T n
def set.has_size {T : Type _} (S n) := ∃ (f : fin n → T), function.injective f ∧ (S = fun.im f)
def set.finite {T : Type _} (S : set T) := ∃ n, set.has_size S n

lemma has_size_zero_iff_empty {T : Type _} :
  ∀ (S : set T), set.has_size S 0 → S = ∅ :=
begin
  intros S h, rw ← subset_of_empty_iff_empty,
  intros x hx, cases h, cases h_h,
  rw h_h_right at hx, cases hx, apply hx_w.elim0
end

theorem subtype_finite_iff_subset_finite {T : Type _} (S : set T)
  : set.finite S ↔ finite (subtype S) :=
begin
  constructor,
  { intros, 
    cases a with n a, cases a with f a, cases a with h h',
    have : ∀ k, S (f k),
    { intros, rw h', existsi k, refl },
    let f' : fin n → subtype S
        := λ k, subtype.mk (f k) (this k),
    existsi n, existsi f',
    constructor,
    { simp [function.injective, f'], exact h },
    { simp [f'], intros y, cases y,
      rewrite h' at y_property,
      cases y_property, existsi y_property_w,
      apply subtype.eq, exact y_property_h } },
  { intros,
    cases a with n a, cases a with f h,
    existsi n,
    let f' : fin n → T := λ k, (f k).val,
    existsi f',
    constructor,
    { dsimp [function.injective, f'],
      intros x y hxy,
      have : f x = f y := subtype.eq hxy,
      apply h.left this },
    { funext, apply propext,
      constructor,
      { intro hx, 
        cases (h.right ⟨x, hx⟩),
        existsi w, dsimp [f'], rw h_1 },
      { intros hx, cases hx, rw ← hx_h,
        rw (_ : f' hx_w = (f hx_w).val),
        exact (f hx_w).property,
        refl } } }
end

theorem classical.subsets_of_finite_sets_are_finite {T}
  : ∀ {S S' : set T}, S ⊆ S' → set.finite S' → set.finite S :=
begin
  suffices : ∀ n S S', S ⊆ S' →
             ∀ (f : fin n → T), function.injective f
                              → (S' = { t : T | ∃ k, f k = t })
                              → set.finite S,
  { intros, cases a_1, cases a_1_h, cases a_1_h_h,
    apply this; assumption },
  intro n, induction n; intros S S' hsub f f_i f_s,
  case nat.zero {
    have : {t : T | ∃ (k : fin 0), f k = t} = ∅,
    { rw ← subset_of_empty_iff_empty, intros x hx,
      cases hx, cases hx_w, cases hx_w_is_lt },
    rw this at f_s,
    { rw f_s at hsub, rw subset_of_empty_iff_empty.mp hsub, 
      existsi 0, existsi f, constructor, assumption, symmetry, assumption } },
  case nat.succ : n ih {
    cases (classical.prop_decidable $ S = S'),
    { have : ∃ x, x ∉ S ∧ x ∈ S',
      { apply classical.by_contradiction,
        intro h',
        apply h,
        funext, apply propext, constructor,
        { apply hsub },
        { intro hx,
            have : ∀ y, ¬(y ∉ S ∧ y ∈ S') := forall_not_of_not_exists h',
            specialize this x,
            apply classical.by_contradiction,
            intro h'', apply this, constructor; assumption } },
      cases this with x hx,
      cases hx with hnxS hxS',
      specialize ih S (S' ∖ {x}) _,
      { rw f_s at hxS', cases hxS' with k hkx,
        let f' := fin.fun_omit k.val f,
        specialize ih f' (omit_inj_if_fun_inj _ _ f_i),
        apply ih, rw f_s,
        funext, apply propext, constructor,
        { intro h, cases h, rw elem_singleton at h_right,
          rw (_ : a ∉ {y : T | y = x} ↔ a ≠ x) at h_right,
          cases h_left with m hm,
          cases nat.lt_trichotomy m.val k.val,
          { existsi fin.mk m.val (nat.lt_of_lt_of_le h_1 $ nat.le_of_lt_succ k.is_lt),
            dsimp [f', fin.fun_omit], rw dif_pos h_1,
            rw ← hm, congr, apply fin.eq_of_veq, refl },
          cases h_1,
          { exfalso, rw (_ : f m = f k) at hm,
            apply h_right, rw ← hm, rw ← hkx,
            congr, apply fin.eq_of_veq, assumption },
          { destruct m.val,
            { intro hm_eq, rw hm_eq at h_1, cases h_1 },
            { intros m' hm_eq,
              have : m' < n,
              { apply nat.lt_of_succ_lt_succ, rw ← hm_eq, exact m.is_lt },
              existsi fin.mk m' this,
              dsimp [f', fin.fun_omit],
              rw dif_neg, rw ← hm, congr,
              apply fin.eq_of_veq, simp, symmetry, assumption,
              { rw hm_eq at h_1, intro,
                exact nat.not_self_lt_lt_succ_self a_1 h_1, } } },
          refl },
        { intro h, cases h with m hm, constructor,
          { dsimp [f', fin.fun_omit] at hm,
            by_cases m.val < k.val,
            { rw dif_pos h at hm,
              existsi fin.mk m.val (nat.lt_trans h k.is_lt), assumption },
            { rw dif_neg h at hm,
              existsi fin.mk (m.val +  1) (nat.succ_lt_succ m.is_lt), 
              rw ← hm } },
          { rw elem_singleton, 
            rw (_ : a ∈ {y : T | y = x} ↔ a = x),
            intro hax, rw hax at hm,
            { rw ← hkx at hm,
              dsimp [f', fin.fun_omit] at hm, 
              by_cases m.val < k.val,
              { apply nat.lt_irrefl k.val, 
                rw dif_pos h at hm,
                have : m.val = k.val := fin.veq_of_eq (f_i hm), 
                rw this at h, exact h },
              { apply h, rw dif_neg h at hm,
                rw ← (fin.veq_of_eq (f_i hm) : m.val + 1 = k.val),
                apply nat.lt_succ_self } },
            refl } } },
      { intro x', cases (classical.prop_decidable $ x = x'),
        { intro hx', have : x' ∈ S' := hsub hx',
          dsimp [(∖), (∈), set.mem],
          rw elem_singleton,
          constructor, assumption,
          apply ne.symm, assumption },
        { intro hx', exfalso, apply hnxS, rw h_1, assumption } } },
    { subst h, existsi (nat.succ n), existsi f, constructor; assumption } }
end

theorem classical.sets_of_finite_types_are_finite
  : ∀ T, finite T → (∀ S : set T, set.finite S) :=
begin
  intros T hT S,
  apply @classical.subsets_of_finite_sets_are_finite T S set.univ (λ x _, true.intro),
  cases hT with n hT, cases hT with f h,
  cases h with f_i f_s,
  existsi n, existsi f,
  constructor, assumption,
  funext, apply propext, rw (_ : set.univ a = true),
  { rw true_iff, exact f_s a },
  refl
end

theorem classical.subtypes_of_finite_types_are_finite
  : ∀ T, finite T → (∀ P : T → Prop, finite (subtype P)) :=
by { intros, rw ← subtype_finite_iff_subset_finite, apply classical.sets_of_finite_types_are_finite, assumption }

lemma surj_zero_implies_eq_zero {T}
  : ∀ (S : set T) n (f : fin n → T) (f' : fin 0 → T),
    (S = fun.im f)
    → (S = fun.im f')
    → n = 0 :=
begin
  intros, by_contradiction,
  let z : fin n := ⟨0, nat.pos_of_ne_zero a_2⟩,
  have : f z ∈ S,
  { rw a, existsi z, refl },
  rw a_1 at this, cases this,
  cases this_w, cases this_w_is_lt
end

theorem one_way_to_be_finite {T}
  : ∀ (S : set T) n (f : fin n → T) n' (f' : fin n' → T),
    function.injective f → (S = fun.im f)
    → function.injective f' → (S = fun.im f')
    → n = n' :=
begin
  intros S n, revert S,
  induction n;
  intros S f n' f' f_i f_s f'_i f'_s,
  { by_contradiction,
    { apply a, symmetry,
      apply surj_zero_implies_eq_zero S n' f' f f'_s f_s } },
  case nat.succ : n ih {
    cases n',
    { exfalso, apply nat.succ_ne_zero n,
      apply surj_zero_implies_eq_zero S _ f f' f_s f'_s },
    let fin_n : fin (nat.succ n) := ⟨n, nat.lt_succ_self n⟩,
    have : f fin_n ∈ S,
    { rw f_s, existsi fin_n, refl },
    rw f'_s at this, cases this with m,
    specialize ih (S ∖ {f fin_n}) (fin.restrict f) n' (fin.fun_omit m.val f'),
    congr, apply ih,
    { rw restrict_is_omit_n, apply omit_inj_if_fun_inj, assumption },
    { rw restrict_is_omit_n,
      suffices : S∖{f fin_n} = fun.im (fin.fun_omit fin_n.val f), { exact this },
      rw im_omit, rw f_s, assumption },
    { apply omit_inj_if_fun_inj, assumption },
    { suffices : S∖{f' m} = fun.im (fin.fun_omit m.val f'), { rw ← this_h, assumption },
      rw im_omit, rw f'_s, assumption } }
end

lemma union_size' {T : Type _} {A B : set T} 
  : disjoint A B
  → ∀ {n m} (f : fin n → T) (g : fin m → T),
    function.injective f → A = fun.im f
    → function.injective g → B = fun.im g
    → function.injective (fin.glue f g)
      ∧ (A ∪ B) = fun.im (fin.glue f g) :=
begin
  intros h n m f g f_i f_s g_i g_s,
  constructor,
  { apply both_inj_and_im_disj_implies_glue_inj f g f_i g_i,
    rw ← f_s, rw ← g_s, assumption },
  { rw [im_glue_eq_union_ims, f_s, g_s] }
end

lemma union_size {T : Type _} {A B : set T}
  : disjoint A B
  → ∀ {n m}, set.has_size A n
           → set.has_size B m
           → set.has_size (A ∪ B) (n + m) :=
begin
  intros hAB n m hA hB,
  cases hA with f hA, cases hA with f_i f_s,
  cases hB with g hB, cases hB with g_i g_s,
  existsi (fin.glue f g), apply union_size'; assumption
end