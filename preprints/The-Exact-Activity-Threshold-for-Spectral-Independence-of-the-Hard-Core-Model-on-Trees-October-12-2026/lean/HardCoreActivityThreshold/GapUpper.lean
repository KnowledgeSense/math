import HardCoreActivityThreshold.HeatBathVariance
import HardCoreActivityThreshold.CorrelationQuadratic

/-! Upper bounds for the actual heat-bath gap from correlation Rayleigh quotients. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem sameOutside_occupation (v w : V) {s t : Finset V}
    (hst : sameOutside v s t) (hw : w ≠ v) : occupation w s = occupation w t := by
  have hm : w ∈ s ↔ w ∈ t := by
    have he : w ∈ s.erase v ↔ w ∈ t.erase v := by rw [hst]
    simpa [mem_erase, hw] using he
  simp only [occupation, hm]

theorem linearOccupation_difference (μ : FiniteLaw (Finset V)) (coeff : V → ℝ) (v : V)
    {s t : Finset V} (hst : sameOutside v s t) :
    linearOccupation μ coeff s - linearOccupation μ coeff t =
      (coeff v / Real.sqrt (occupationVariance μ v)) * (occupation v s - occupation v t) := by
  unfold linearOccupation
  rw [← sum_sub_distrib]
  calc
    (∑ w, (coeff w * normalizedOccupation μ w s - coeff w * normalizedOccupation μ w t)) =
        coeff v * normalizedOccupation μ v s - coeff v * normalizedOccupation μ v t := by
      apply sum_eq_single v
      · intro w _ hw
        unfold normalizedOccupation
        rw [sameOutside_occupation v w hst hw]
        ring
      · intro hv
        exact False.elim (hv (mem_univ v))
    _ = _ := by unfold normalizedOccupation; ring

theorem siteDirichletForm_linearOccupation (μ : FiniteLaw (Finset V)) (coeff : V → ℝ) (v : V) :
    siteDirichletForm μ v (linearOccupation μ coeff) =
      (coeff v / Real.sqrt (occupationVariance μ v)) ^ 2 * siteDirichletForm μ v (occupation v) := by
  unfold siteDirichletForm
  rw [← mul_div_assoc]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro s _
  rw [mul_sum]
  apply sum_congr rfl
  intro t _
  by_cases hst : sameOutside v s t
  · rw [linearOccupation_difference μ coeff v hst]
    ring
  · simp [singleSiteKernel, hst]

theorem siteDirichletForm_linearOccupation_le (μ : FiniteLaw (Finset V)) (coeff : V → ℝ)
    (v : V) (hv : 0 < occupationVariance μ v) :
    siteDirichletForm μ v (linearOccupation μ coeff) ≤ coeff v ^ 2 := by
  rw [siteDirichletForm_linearOccupation, siteDirichletForm_eq_conditionalVariance]
  calc
    (coeff v / Real.sqrt (occupationVariance μ v))^2 * siteConditionalVariance μ v (occupation v) ≤
        (coeff v / Real.sqrt (occupationVariance μ v))^2 * occupationVariance μ v :=
      mul_le_mul_of_nonneg_left (siteConditionalVariance_le_variance μ v (occupation v)) (sq_nonneg _)
    _ = coeff v ^ 2 := by
      rw [div_pow, Real.sq_sqrt hv.le]
      exact div_mul_cancel₀ _ hv.ne'

theorem dirichletForm_linearOccupation_le (μ : FiniteLaw (Finset V)) (coeff : V → ℝ)
    (hvar : ∀ v, 0 < occupationVariance μ v) :
    dirichletForm μ (linearOccupation μ coeff) ≤ (∑ v, coeff v ^ 2) / Fintype.card V := by
  rw [dirichletForm_eq_mean_conditionalVariance]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro v _
  rw [← siteDirichletForm_eq_conditionalVariance]
  exact siteDirichletForm_linearOccupation_le μ coeff v (hvar v)

/-- A correlation Rayleigh quotient bounds the actual heat-bath gap from above. -/
theorem heatBathGap_le_correlation_rayleigh (μ : FiniteLaw (Finset V)) (coeff : V → ℝ)
    (hvar : ∀ v, 0 < occupationVariance μ v)
    (hq : 0 < ∑ u, ∑ v, coeff u * correlationMatrix μ u v * coeff v) :
    heatBathGap μ ≤ (∑ v, coeff v ^ 2) /
      ((Fintype.card V : ℝ) * (∑ u, ∑ v, coeff u * correlationMatrix μ u v * coeff v)) := by
  have hf : 0 < μ.variance (linearOccupation μ coeff) := by
    rw [← correlation_quadratic_variance]
    exact hq
  calc
    heatBathGap μ ≤ dirichletForm μ (linearOccupation μ coeff) /
        μ.variance (linearOccupation μ coeff) := heatBathGap_le_rayleigh μ _ hf
    _ ≤ ((∑ v, coeff v ^ 2) / Fintype.card V) /
        μ.variance (linearOccupation μ coeff) :=
      div_le_div_of_nonneg_right (dirichletForm_linearOccupation_le μ coeff hvar) hf.le
    _ = _ := by rw [← correlation_quadratic_variance]; ring

end HardCoreActivityThreshold
