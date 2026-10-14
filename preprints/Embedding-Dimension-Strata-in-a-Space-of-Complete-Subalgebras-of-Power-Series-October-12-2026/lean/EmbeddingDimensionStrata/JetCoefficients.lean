import EmbeddingDimensionStrata.PolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Exact coefficient coordinates on the genuine quotient algebra -/
noncomputable section
namespace EmbeddingDimensionStrata
variable {K : Type*} [Field K]

/-- A coefficient below the cutoff descends to the quotient. -/
def jetCoeff (c : ℕ) (i : Fin c) : Jet K c →ₗ[K] K where
  toFun := Quotient.lift (fun f : PowerSeries K => PowerSeries.coeff i.val f) (by
    intro f g hfg
    exact (jetMap_eq_iff c f g).mp (Quotient.sound hfg) i.val i.isLt)
  map_add' := by
    intro x y
    obtain ⟨f, rfl⟩ := jetMap_surjective c x
    obtain ⟨g, rfl⟩ := jetMap_surjective c y
    exact (PowerSeries.coeff i.val).map_add f g
  map_smul' := by
    intro a x
    obtain ⟨f, rfl⟩ := jetMap_surjective c x
    exact (PowerSeries.coeff i.val).map_smul a f

@[simp]
theorem jetCoeff_jetMap (c : ℕ) (i : Fin c) (f : PowerSeries K) :
    jetCoeff c i (jetMap K c f) = PowerSeries.coeff i.val f := rfl

/-- Coefficients give exact coordinates on the semantic quotient. -/
def jetCoefficients (c : ℕ) : Jet K c →ₗ[K] (Fin c → K) :=
  LinearMap.pi (jetCoeff c)

@[simp]
theorem jetCoefficients_jetMap (c : ℕ) (f : PowerSeries K) (i : Fin c) :
    jetCoefficients c (jetMap K c f) i = PowerSeries.coeff i.val f := rfl

theorem jetCoefficients_injective (c : ℕ) :
    Function.Injective (jetCoefficients (K := K) c) := by
  intro x y hxy
  obtain ⟨f, rfl⟩ := jetMap_surjective c x
  obtain ⟨g, rfl⟩ := jetMap_surjective c y
  apply (jetMap_eq_iff c f g).mpr
  intro i hi
  exact congrFun hxy ⟨i, hi⟩

theorem jetCoefficients_surjective (c : ℕ) :
    Function.Surjective (jetCoefficients (K := K) c) := by
  intro a
  refine ⟨jetMap K c (PowerSeries.mk fun n => if hn : n < c then a ⟨n, hn⟩ else 0), ?_⟩
  funext i
  simp only [jetCoefficients_jetMap, PowerSeries.coeff_mk, dite_eq_left i.isLt]

/-- The finite coefficient space is proved equivalent to the quotient algebra.
Subsequent finite-dimensional computations may therefore be transported back
to actual power-series subalgebras. -/
def jetCoefficientsEquiv (c : ℕ) : Jet K c ≃ₗ[K] (Fin c → K) :=
  LinearEquiv.ofBijective (jetCoefficients c)
    ⟨jetCoefficients_injective c, jetCoefficients_surjective c⟩

instance jet_finite (c : ℕ) : Module.Finite K (Jet K c) :=
  Module.Finite.of_injective (jetCoefficients c) (jetCoefficients_injective c)

theorem jet_finrank (c : ℕ) : Module.finrank K (Jet K c) = c := by
  rw [(jetCoefficientsEquiv (K := K) c).finrank_eq, Module.finrank_fin_fun]

end EmbeddingDimensionStrata
