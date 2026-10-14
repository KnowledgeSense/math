import HardCoreActivityThreshold.CorrelationQuadratic
import HardCoreActivityThreshold.FiniteVariance

/-! A correlation quadratic bound controls the response of every square-integrable statistic. -/
namespace HardCoreActivityThreshold
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The quadratic-form version of the correlation operator bound. -/
def CorrelationBound (μ : FiniteLaw (Finset V)) (C : ℝ) : Prop :=
  ∀ a : V → ℝ, (∑ u, ∑ v, a u * correlationMatrix μ u v * a v) ≤ C * ∑ v, a v ^ 2

theorem CorrelationBound.mono {μ : FiniteLaw (Finset V)} {C D : ℝ}
    (h : CorrelationBound μ C) (hCD : C ≤ D) : CorrelationBound μ D := by
  intro a
  exact (h a).trans (mul_le_mul_of_nonneg_right hCD (sum_nonneg (fun v _ => sq_nonneg _)))

theorem covariance_normalizedOccupation (μ : FiniteLaw (Finset V))
    (f : Finset V → ℝ) (v : V) :
    μ.covariance f (normalizedOccupation μ v) =
      μ.covariance f (occupation v) / Real.sqrt (occupationVariance μ v) := by
  unfold normalizedOccupation
  have he : (fun s => (occupation v s - marginal μ v) /
      Real.sqrt (occupationVariance μ v)) =
      fun s => (Real.sqrt (occupationVariance μ v))⁻¹ * (occupation v s - marginal μ v) := by
    funext s
    ring
  rw [he, μ.covariance_smul_right, μ.covariance_sub_const_right]
  ring

/-- Bessel's inequality with the optimal upper correlation bound; zero-variance coordinates are allowed. -/
theorem CorrelationBound.covariance_normalized_sum_le {μ : FiniteLaw (Finset V)} {C : ℝ}
    (hC : 0 ≤ C) (h : CorrelationBound μ C) (f : Finset V → ℝ) :
    (∑ v, μ.covariance f (normalizedOccupation μ v)^2) ≤ C * μ.variance f := by
  let b : V → ℝ := fun v => μ.covariance f (normalizedOccupation μ v)
  have hcross : μ.covariance f (linearOccupation μ b) = ∑ v, b v ^ 2 := by
    unfold linearOccupation
    rw [μ.covariance_sum_right]
    simp_rw [μ.covariance_smul_right]
    apply sum_congr rfl
    intro v _
    exact (pow_two (b v)).symm
  have hvar : μ.variance (linearOccupation μ b) ≤ C * ∑ v, b v ^ 2 := by
    rw [← correlation_quadratic_variance]
    exact h b
  have hcs := μ.covariance_sq_le f (linearOccupation μ b)
  rw [hcross] at hcs
  have hmul := mul_le_mul_of_nonneg_left hvar (μ.variance_nonneg f)
  have hsum : 0 ≤ ∑ v, b v ^ 2 := sum_nonneg (fun v _ => sq_nonneg _)
  change (∑ v, b v ^ 2) ≤ C * μ.variance f
  by_cases hz : (∑ v, b v ^ 2) = 0
  · rw [hz]
    exact mul_nonneg hC (μ.variance_nonneg f)
  · have hpos : 0 < ∑ v, b v ^ 2 := lt_of_le_of_ne hsum (Ne.symm hz)
    nlinarith

/-- The occupation means, rather than variances, are the denominators for positive reveals. -/
theorem CorrelationBound.covariance_mean_sum_le {μ : FiniteLaw (Finset V)} {C : ℝ}
    (hC : 0 ≤ C) (h : CorrelationBound μ C) (f : Finset V → ℝ) :
    (∑ v, μ.covariance f (occupation v)^2 / marginal μ v) ≤ C * μ.variance f := by
  apply le_trans _ (h.covariance_normalized_sum_le hC f)
  apply sum_le_sum
  intro v _
  rw [covariance_normalizedOccupation, div_pow,
    Real.sq_sqrt (show 0 ≤ occupationVariance μ v from μ.variance_nonneg _)]
  by_cases hz : occupationVariance μ v = 0
  · have hc := μ.covariance_eq_zero_of_variance_eq_zero f (occupation v) hz
    rw [hc, zero_pow (by decide), zero_div, zero_div]
  · have hv : 0 < occupationVariance μ v := lt_of_le_of_ne (μ.variance_nonneg _) (Ne.symm hz)
    have he : occupationVariance μ v = marginal μ v * (1 - marginal μ v) :=
      occupation_variance μ v
    have hm := marginal_nonneg μ v
    have hle : occupationVariance μ v ≤ marginal μ v := by
      rw [he]
      nlinarith
    exact div_le_div_of_nonneg_left (sq_nonneg _) hv hle

end HardCoreActivityThreshold
