import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section
namespace HilbertBipartite
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

/-- Exponents of products of exactly `s` chosen monomial generators. -/
def generatorPowerExponents (G : Set (σ →₀ ℕ)) : ℕ → Set (σ →₀ ℕ)
  | 0 => {0}
  | s+1 => {a | ∃ b ∈ G, ∃ c ∈ generatorPowerExponents G s, a = b+c}

/-- The monomial ideal determined by its generating exponents. -/
def monomialIdeal (G : Set (σ →₀ ℕ)) : Ideal (MvPolynomial σ K) :=
  Ideal.span ((fun a => monomial a (1 : K)) '' G)

open scoped Pointwise in
theorem monomialIdeal_pow (G : Set (σ →₀ ℕ)) (s : ℕ) :
    monomialIdeal (K := K) G ^ s = monomialIdeal (generatorPowerExponents G s) := by
  induction s with
  | zero =>
    simp [monomialIdeal, generatorPowerExponents, Ideal.span_singleton_one]
  | succ s ih =>
    rw [pow_succ', ih]
    unfold monomialIdeal
    rw [Ideal.span_mul_span]
    congr 1
    ext f
    simp only [Set.mem_mul, Set.mem_image, generatorPowerExponents, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a+b, ⟨a, ha, b, hb, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨monomial a 1, ⟨a, ha, rfl⟩,
        monomial b 1, ⟨b, hb, rfl⟩, by simp⟩

theorem mem_monomialIdeal_pow_iff (G : Set (σ →₀ ℕ)) (s : ℕ)
    (f : MvPolynomial σ K) :
    f ∈ monomialIdeal G ^ s ↔
      ∀ a ∈ f.support, ∃ b ∈ generatorPowerExponents G s, b ≤ a := by
  rw [monomialIdeal_pow, monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image]

/-- The quadratic generators: all vertex squares and all cross-part products. -/
def bipartiteGeneratorExponents (p q : ℕ) : Set ((Fin p ⊕ Fin q) →₀ ℕ) :=
  {a | (∃ i, a = Finsupp.single i 2) ∨
    ∃ i : Fin p, ∃ j : Fin q,
      a = Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1}

/-- The complete bipartite quadratic ideal, including all variable squares. -/
def bipartiteIdeal (K : Type*) [Field K] (p q : ℕ) :
    Ideal (MvPolynomial (Fin p ⊕ Fin q) K) :=
  monomialIdeal (bipartiteGeneratorExponents p q)

/-- The defining generators are exactly the squares and complete bipartite edges. -/
theorem bipartiteIdeal_eq_span (p q : ℕ) :
    bipartiteIdeal K p q = Ideal.span
      (Set.range (fun i : Fin p ⊕ Fin q => (X i : MvPolynomial _ K)^2) ∪
       Set.range (fun ij : Fin p × Fin q =>
         (X (Sum.inl ij.1) : MvPolynomial _ K) * X (Sum.inr ij.2))) := by
  unfold bipartiteIdeal monomialIdeal
  congr 1
  ext f
  simp only [Set.mem_image, bipartiteGeneratorExponents, Set.mem_ofPred_eq,
    Set.mem_union, Set.mem_range]
  constructor
  · rintro ⟨a, (⟨i, rfl⟩ | ⟨i, j, rfl⟩), rfl⟩
    · exact Or.inl ⟨i, by simp [X_pow_eq_monomial]⟩
    · exact Or.inr ⟨(i,j), by simp [X]⟩
  · rintro (⟨i, rfl⟩ | ⟨⟨i,j⟩, rfl⟩)
    · exact ⟨Finsupp.single i 2, Or.inl ⟨i, rfl⟩, by simp [X_pow_eq_monomial]⟩
    · exact ⟨Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1,
        Or.inr ⟨i,j,rfl⟩, by simp [X]⟩

/-- Exponents divisible by a product of `s` quadratic generators. -/
def bipartitePowerExponents (p q s : ℕ) : Set ((Fin p ⊕ Fin q) →₀ ℕ) :=
  {a | ∃ b ∈ generatorPowerExponents (bipartiteGeneratorExponents p q) s, b ≤ a}

theorem mem_bipartiteIdeal_pow_iff_support (p q s : ℕ)
    (f : MvPolynomial (Fin p ⊕ Fin q) K) :
    f ∈ bipartiteIdeal K p q ^ s ↔
      ∀ a ∈ f.support, a ∈ bipartitePowerExponents p q s :=
  mem_monomialIdeal_pow_iff _ _ _

/-- A basis for every actual power quotient, with no dimension hypothesis. -/
noncomputable def bipartitePowerQuotientBasis (p q s : ℕ) :
    Module.Basis ↥((bipartitePowerExponents p q s)ᶜ) K
      (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s) :=
  standardMonomialBasis _ _ (mem_bipartiteIdeal_pow_iff_support p q s)

end HilbertBipartite
