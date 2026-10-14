import HonestEmbeddingDimension.AnalyticTaylor
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Data.Set.Finite.Lattice

namespace HonestEmbeddingDimension

/-- A numerical semigroup is an actual cofinite additive submonoid of the natural numbers. -/
structure NumericalSemigroup where
  monoid : AddSubmonoid ℕ
  finite_complement : (monoid : Set ℕ)ᶜ.Finite

/-- Multiplicity is specified by its defining least-positive-member property. -/
def HasMultiplicity (S : NumericalSemigroup) (m : ℕ) : Prop :=
  0 < m ∧ m ∈ S.monoid ∧ ∀ n ∈ S.monoid, 0 < n → m ≤ n

/-- Realization by genuine convergent complex coordinate germs. -/
def AnalyticallyRealizes (S : NumericalSemigroup) (d : ℕ) : Prop :=
  ∃ F : ℂ → Fin d → ℂ, (∀ i, AnalyticAt ℂ (fun t => F t i) 0) ∧
    F 0 = 0 ∧ analyticValues F = (S.monoid : Set ℕ)

/-- The honest embedding dimension, expressed without a convention for an empty infimum. -/
def HasHonestEmbeddingDimension (S : NumericalSemigroup) (d : ℕ) : Prop :=
  AnalyticallyRealizes S d ∧ ∀ e, AnalyticallyRealizes S e → d ≤ e

/-- A formal realization uses the actual multivariate substitution value algebra. -/
def FormallyRealizes (S : NumericalSemigroup) (d : ℕ) : Prop :=
  ∃ f : Fin d → PowerSeries ℂ, (∀ i, (f i).constantCoeff = 0) ∧
    formalValues f = (S.monoid : Set ℕ)

/-- Every genuine analytic realization gives a formal realization through its actual Taylor series. -/
theorem AnalyticallyRealizes.formal {S : NumericalSemigroup} {d : ℕ}
    (h : AnalyticallyRealizes S d) : FormallyRealizes S d := by
  obtain ⟨F, hF, hF0, hvalues⟩ := h
  refine ⟨fun i => analyticTaylor (fun t => F t i), ?_, ?_⟩
  · intro i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [analyticTaylor, hF0]
  · rw [← analyticValues_eq_formalValues F hF hF0]
    exact hvalues

end HonestEmbeddingDimension
