import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section
namespace FourGeneratedSemigroups
open MvPolynomial
variable {σ K : Type*} [Field K]

/-- Retain precisely the coefficients at standard exponents. -/
noncomputable def standardCoefficientMap (U : Set (σ →₀ ℕ)) :
    MvPolynomial σ K →ₗ[K] (↥(Uᶜ) →₀ K) :=
  (Finsupp.lcomapDomain Subtype.val Subtype.val_injective).comp
    (MvPolynomial.basisMonomials σ K).repr.toLinearMap

@[simp] theorem standardCoefficientMap_apply (U : Set (σ →₀ ℕ))
    (f : MvPolynomial σ K) (a : ↥(Uᶜ)) :
    standardCoefficientMap U f a = f.coeff a := rfl

theorem standardCoefficientMap_surjective (U : Set (σ →₀ ℕ)) :
    Function.Surjective (standardCoefficientMap (K := K) U) := by
  intro f
  refine ⟨(MvPolynomial.basisMonomials σ K).repr.symm
    (Finsupp.mapDomain Subtype.val f), ?_⟩
  simp only [standardCoefficientMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact Finsupp.leftInverse_lcomapDomain_mapDomain Subtype.val Subtype.val_injective f

/-- A support-defined monomial ideal is the kernel of standard-coefficient extraction. -/
theorem standardCoefficientMap_ker (I : Ideal (MvPolynomial σ K))
    (U : Set (σ →₀ ℕ))
    (hI : ∀ f : MvPolynomial σ K, f ∈ I ↔ ∀ a ∈ f.support, a ∈ U) :
    LinearMap.ker (standardCoefficientMap (K := K) U) = I.restrictScalars K := by
  ext f
  simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem]
  rw [hI]
  constructor
  · intro h a ha
    by_contra hnot
    have hz := congrArg (fun g : ↥(Uᶜ) →₀ K => g ⟨a, hnot⟩) h
    exact (MvPolynomial.mem_support_iff.mp ha) hz
  · intro h
    ext a
    apply Classical.byContradiction
    intro hn
    exact a.property (h a (MvPolynomial.mem_support_iff.mpr hn))

/-- Standard coefficients identify a monomial quotient with finitely supported
functions on its standard exponents. -/
noncomputable def standardQuotientEquiv (I : Ideal (MvPolynomial σ K))
    (U : Set (σ →₀ ℕ))
    (hI : ∀ f : MvPolynomial σ K, f ∈ I ↔ ∀ a ∈ f.support, a ∈ U) :
    (MvPolynomial σ K ⧸ I) ≃ₗ[K] (↥(Uᶜ) →₀ K) :=
  (Submodule.quotEquivOfEq (I.restrictScalars K)
    (LinearMap.ker (standardCoefficientMap (K := K) U))
    (standardCoefficientMap_ker I U hI).symm).trans
    ((standardCoefficientMap (K := K) U).quotKerEquivOfSurjective
      (standardCoefficientMap_surjective (K := K) U))

@[simp] theorem standardQuotientEquiv_mk (I : Ideal (MvPolynomial σ K))
    (U : Set (σ →₀ ℕ))
    (hI : ∀ f : MvPolynomial σ K, f ∈ I ↔ ∀ a ∈ f.support, a ∈ U)
    (f : MvPolynomial σ K) :
    standardQuotientEquiv I U hI (Ideal.Quotient.mk I f) =
      standardCoefficientMap U f := by
  rfl

/-- The standard monomials form a basis of the actual polynomial quotient. -/
noncomputable def standardMonomialBasis (I : Ideal (MvPolynomial σ K))
    (U : Set (σ →₀ ℕ))
    (hI : ∀ f : MvPolynomial σ K, f ∈ I ↔ ∀ a ∈ f.support, a ∈ U) :
    Module.Basis ↥(Uᶜ) K (MvPolynomial σ K ⧸ I) :=
  (Finsupp.basisSingleOne : Module.Basis ↥(Uᶜ) K (↥(Uᶜ) →₀ K)).map
    (standardQuotientEquiv I U hI).symm

@[simp] theorem standardMonomialBasis_apply (I : Ideal (MvPolynomial σ K))
    (U : Set (σ →₀ ℕ))
    (hI : ∀ f : MvPolynomial σ K, f ∈ I ↔ ∀ a ∈ f.support, a ∈ U)
    (a : ↥(Uᶜ)) :
    standardMonomialBasis I U hI a = Ideal.Quotient.mk I (monomial a 1) := by
  classical
  apply (standardQuotientEquiv I U hI).injective
  simp only [standardMonomialBasis, Module.Basis.map_apply,
    LinearEquiv.apply_symm_apply, Finsupp.coe_basisSingleOne, standardQuotientEquiv_mk]
  ext b
  simp [Finsupp.single_apply, MvPolynomial.coeff_monomial, Subtype.ext_iff]

theorem finrank_monomial_quotient (I : Ideal (MvPolynomial σ K))
    (U : Set (σ →₀ ℕ)) [Fintype ↥(Uᶜ)]
    (hI : ∀ f : MvPolynomial σ K, f ∈ I ↔ ∀ a ∈ f.support, a ∈ U) :
    Module.finrank K (MvPolynomial σ K ⧸ I) = Fintype.card ↥(Uᶜ) :=
  Module.finrank_eq_card_basis (standardMonomialBasis I U hI)


end FourGeneratedSemigroups
