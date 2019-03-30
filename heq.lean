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

lemma dep_fn_eq_of_heq
  {A : Type u} (B : A → Type v)
  (C : Type w) (f : Π x : A, B x → C)
  {a a' : A} {b : B a} {b' : B a'}
  : a = a' → b == b' → f a b = f a' b' :=
by { intro p, cases p, intro p', cases eq_of_heq p', refl }

lemma fin.funext (C : Type w) {n k : nat}
                 (p : n = k)
  : ∀ (f : fin n → C) (g : fin k → C),
      (∀ x : fin n, f x = g ⟨x.val, p ▸ x.is_lt⟩) → f == g :=
by { cases p, intros, apply heq_of_eq, funext, rw a x, congr, apply fin.eq_of_veq, refl }

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