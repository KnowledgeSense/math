import EmbeddingDimensionStrata.RelationImage
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Dimension of the actual cotangent module -/
noncomputable section
namespace EmbeddingDimensionStrata
variable {K : Type*} [Field K]

/-- Rank-nullity on a subspace, expressed in its ambient space. -/
theorem finrank_map_add_inf_ker {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (S : Submodule K V) (f : V →ₗ[K] W) :
    Module.finrank K (S.map f) + Module.finrank K ↥(S ⊓ LinearMap.ker f) = Module.finrank K S := by
  have hh := LinearMap.finrank_range_add_finrank_ker (f.comp S.subtype)
  have hr : LinearMap.range (f.comp S.subtype) = S.map f := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩; exact ⟨y,y.property,rfl⟩
    · rintro ⟨y,hy,rfl⟩; exact ⟨⟨y,hy⟩,rfl⟩
  have hk : (LinearMap.ker (f.comp S.subtype)).map S.subtype = S ⊓ LinearMap.ker f := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact ⟨y.property,hy⟩
    · rintro ⟨hx,hy⟩; exact ⟨⟨x,hx⟩,hy,rfl⟩
  rw [hr] at hh
  rw [← hk, Submodule.finrank_map_subtype_eq]
  exact hh

theorem degreeSpace_two_finrank (p : ParameterSpace (K := K)) :
    Module.finrank K (monomialDegreeSpace p.val 2) =
      21 + Module.finrank K (relationVectorSpace p.val) := by
  have hh := finrank_map_add_inf_ker (monomialDegreeSpace p.val 2) (linearTerms p.val)
  rw [square_linearTerms_image p, degreeSpace_two_inf_ker p, decomposableJetSpace_finrank] at hh
  omega

theorem augmentationIdeal_finrank (p : ParameterSpace (K := K)) :
    Module.finrank K (augmentationIdeal p.val) = 26 := by
  have hh := LinearMap.finrank_range_add_finrank_ker (parameterAugmentation p.val).toLinearMap
  have hr : LinearMap.range (parameterAugmentation p.val).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr (parameterAugmentation_surjective p.val)
  rw [hr, finrank_top, Module.finrank_self, parameterJetAlgebra_finrank p] at hh
  change 1 + Module.finrank K (augmentationIdeal p.val) = 27 at hh
  omega

theorem augmentationIdeal_square_finrank (p : ParameterSpace (K := K)) :
    Module.finrank K ↥(augmentationIdeal p.val ^ 2) =
      21 + Module.finrank K (relationVectorSpace p.val) := by
  have heq := (Submodule.equivMapOfInjective (parameterJetAlgebra p.val).val.toLinearMap
    (by intro x y h; exact Subtype.ext h) ((augmentationIdeal p.val ^ 2).restrictScalars K)).finrank_eq
  rw [augmentationIdeal_square_image, degreeSpace_two_finrank p] at heq
  exact heq

theorem cotangentKernel_finrank (p : ParameterSpace (K := K)) :
    Module.finrank K (LinearMap.ker ((augmentationIdeal p.val).toCotangent.restrictScalars K)) =
      Module.finrank K ↥(augmentationIdeal p.val ^ 2) := by
  let I := augmentationIdeal p.val
  have hk : (LinearMap.ker (I.toCotangent.restrictScalars K)).map
      (I.restrictScalars K).subtype = (I ^ 2).restrictScalars K := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (I.toCotangent_eq_zero y).mp hy
    · intro hx
      have hxI : x ∈ I := (Ideal.pow_le_self (by omega : 2 ≠ 0)) hx
      exact ⟨⟨x,hxI⟩,(I.toCotangent_eq_zero ⟨x,hxI⟩).mpr hx,rfl⟩
  have hd := Submodule.finrank_map_subtype_eq (I.restrictScalars K)
    (LinearMap.ker (I.toCotangent.restrictScalars K))
  exact hd.symm.trans (congrArg (fun S : Submodule K (parameterJetAlgebra p.val) =>
    Module.finrank K S) hk)

/-- The embedding dimension is computed from the genuine maximal ideal
cotangent module, with precisely the two reduced binomial relation vectors. -/
theorem embeddingDimension_relation_rank (p : ParameterSpace (K := K)) :
    embeddingDimension p = 5 - Module.finrank K (relationVectorSpace p.val) := by
  have hh := LinearMap.finrank_range_add_finrank_ker
    ((augmentationIdeal p.val).toCotangent.restrictScalars K)
  have hr : LinearMap.range ((augmentationIdeal p.val).toCotangent.restrictScalars K) = ⊤ :=
    LinearMap.range_eq_top.mpr (augmentationIdeal p.val).toCotangent_surjective
  rw [hr, finrank_top, cotangentKernel_finrank p, augmentationIdeal_square_finrank p,
    augmentationIdeal_finrank p] at hh
  change embeddingDimension p + (21 + Module.finrank K (relationVectorSpace p.val)) = 26 at hh
  omega

end EmbeddingDimensionStrata
