import HardCoreActivityThreshold.Correlation

/-! Correlation quadratic forms are the variances of actual normalized linear statistics. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def normalizedOccupation (μ : FiniteLaw (Finset V)) (v : V)
    (s : Finset V) : ℝ := (occupation v s - marginal μ v) / Real.sqrt (occupationVariance μ v)

@[simp] theorem normalizedOccupation_mean (μ : FiniteLaw (Finset V)) (v : V) :
    μ.expectation (normalizedOccupation μ v) = 0 := by
  unfold normalizedOccupation
  simp_rw [div_eq_mul_inv, mul_comm (_ - _)]
  rw [μ.expectation_smul, μ.expectation_sub, μ.expectation_const]
  change _ * (marginal μ v - marginal μ v) = 0
  ring

theorem normalizedOccupation_product (μ : FiniteLaw (Finset V)) (u v : V) :
    μ.expectation (fun s => normalizedOccupation μ u s * normalizedOccupation μ v s) =
      correlationMatrix μ u v := by
  unfold normalizedOccupation correlationMatrix occupationCovariance FiniteLaw.covariance
  have hsqrt : Real.sqrt (occupationVariance μ u * occupationVariance μ v) =
      Real.sqrt (occupationVariance μ u) * Real.sqrt (occupationVariance μ v) :=
    Real.sqrt_mul (μ.variance_nonneg _) _
  rw [hsqrt]
  have h (s : Finset V) :
      (occupation u s - marginal μ u) / Real.sqrt (occupationVariance μ u) *
        ((occupation v s - marginal μ v) / Real.sqrt (occupationVariance μ v)) =
      (Real.sqrt (occupationVariance μ u) * Real.sqrt (occupationVariance μ v))⁻¹ *
        ((occupation u s - marginal μ u) * (occupation v s - marginal μ v)) := by ring
  simp_rw [h]
  rw [μ.expectation_smul]
  unfold marginal
  ring

noncomputable def linearOccupation (μ : FiniteLaw (Finset V)) (coeff : V → ℝ)
    (s : Finset V) : ℝ := ∑ v, coeff v * normalizedOccupation μ v s

@[simp] theorem linearOccupation_mean (μ : FiniteLaw (Finset V)) (coeff : V → ℝ) :
    μ.expectation (linearOccupation μ coeff) = 0 := by
  unfold linearOccupation
  rw [μ.expectation_sum]
  simp_rw [μ.expectation_smul, normalizedOccupation_mean, mul_zero]
  simp

/-- This quadratic form is not an abstract proxy: it equals the actual statistic's variance. -/
theorem correlation_quadratic_variance (μ : FiniteLaw (Finset V)) (coeff : V → ℝ) :
    (∑ u, ∑ v, coeff u * correlationMatrix μ u v * coeff v) =
      μ.variance (linearOccupation μ coeff) := by
  rw [μ.variance_eq_second_moment, linearOccupation_mean, sq, zero_mul, sub_zero]
  have h (s : Finset V) : linearOccupation μ coeff s ^ 2 =
      ∑ u, ∑ v, (coeff u * coeff v) *
        (normalizedOccupation μ u s * normalizedOccupation μ v s) := by
    unfold linearOccupation
    rw [pow_two, sum_mul]
    apply sum_congr rfl
    intro u _
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    ring
  simp_rw [h]
  rw [μ.expectation_sum]
  simp_rw [μ.expectation_sum, μ.expectation_smul, normalizedOccupation_product]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  ring

theorem correlation_quadratic_nonneg (μ : FiniteLaw (Finset V)) (coeff : V → ℝ) :
    0 ≤ ∑ u, ∑ v, coeff u * correlationMatrix μ u v * coeff v := by
  rw [correlation_quadratic_variance]
  exact μ.variance_nonneg _

end HardCoreActivityThreshold
