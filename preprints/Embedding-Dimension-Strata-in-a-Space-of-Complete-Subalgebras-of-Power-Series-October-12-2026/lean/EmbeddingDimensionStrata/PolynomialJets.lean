import EmbeddingDimensionStrata.JetCorrespondence
import Mathlib.Algebra.Polynomial.Div

/-! # Identifying the semantic jet quotient with `K[t]/(t^c)` -/
noncomputable section
namespace EmbeddingDimensionStrata
variable {K : Type*} [Field K]

/-- Inclusion of polynomials followed by the genuine power-series quotient. -/
def polynomialJetMap (c : ℕ) : Polynomial K →ₐ[K] Jet K c :=
  (jetMap K c).comp (Polynomial.coeToPowerSeries.algHom K)

theorem polynomialJetMap_apply (c : ℕ) (f : Polynomial K) :
    polynomialJetMap c f = jetMap K c (f : PowerSeries K) := by
  simp [polynomialJetMap, Polynomial.coeToPowerSeries.algHom_apply]

theorem jetMap_trunc (c : ℕ) (f : PowerSeries K) :
    jetMap K c (f.trunc c : PowerSeries K) = jetMap K c f := by
  apply (jetMap_eq_iff c _ _).mpr
  intro i hi
  exact PowerSeries.coeff_coe_trunc_of_lt hi

theorem polynomialJetMap_surjective (c : ℕ) :
    Function.Surjective (polynomialJetMap (K := K) c) := by
  intro q
  obtain ⟨f, rfl⟩ := jetMap_surjective c q
  exact ⟨f.trunc c, (polynomialJetMap_apply c _).trans (jetMap_trunc c f)⟩

theorem polynomialJetMap_ker (c : ℕ) :
    RingHom.ker (polynomialJetMap (K := K) c).toRingHom =
      Ideal.span {(Polynomial.X : Polynomial K) ^ c} := by
  ext f
  change polynomialJetMap c f = 0 ↔ _
  rw [polynomialJetMap_apply, jetMap_eq_zero_iff, Ideal.mem_span_singleton,
    Polynomial.X_pow_dvd_iff]
  simp only [InTail, Polynomial.coeff_coe]

/-- The finite jet object used in the subalgebra correspondence is algebraically
isomorphic to the paper's polynomial quotient `K[t]/(t^c)`. -/
def polynomialJetEquiv (c : ℕ) :
    (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ c}) ≃ₐ[K] Jet K c :=
  (Ideal.quotientEquivAlgOfEq K (polynomialJetMap_ker c).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (polynomialJetMap_surjective c))

end EmbeddingDimensionStrata
