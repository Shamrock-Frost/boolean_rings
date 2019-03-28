import .algebra_util .boolean_rings

@[reducible]
def ring_of_subsets (A) := set A

theorem classification_of_finite_boolean_rings 
  {R : Type} [boolean_ring R]
  : finite R → ∃ A : Type, R ≅ ring_of_subsets A :=
begin
  intros is_fin,
  existsi min_nonzero.type,
  apply ring.isomorphic_symm,
  existsi min_nonzero.pset_embed is_fin,
  apply classical.ring.bijective_homomorphism_is_isomorphism,
  { constructor,
    { exact pset_embed_inj is_fin },
    { exact pset_embed_surj is_fin } },
  { constructor,
    exact pset_embed_preserves_add is_fin,
    constructor,
    { exact pset_embed_preserves_mul is_fin },
    { exact pset_embed_preserves_one is_fin } }
end