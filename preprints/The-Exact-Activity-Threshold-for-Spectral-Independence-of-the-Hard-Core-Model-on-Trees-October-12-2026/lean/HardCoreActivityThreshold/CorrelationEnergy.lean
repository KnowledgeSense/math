import HardCoreActivityThreshold.ResponseEnergy
import HardCoreActivityThreshold.TreeRootCorrelation

/-! Squared occupation responses force a large row of the actual correlation matrix. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem occupationVariance_le_quarter (μ : FiniteLaw (Finset V)) (v : V) :
    occupationVariance μ v ≤ 1/4 := by
  unfold occupationVariance
  rw [occupation_variance]
  nlinarith [sq_nonneg (marginal μ v - 1/2)]

theorem root_occupationVariance (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) :
    occupationVariance (hardCoreLaw A.root.graph activity ha) none =
      downwardOccupation A activity * (1-downwardOccupation A activity) := by
  unfold occupationVariance
  rw [occupation_variance, ← forestMarginal_free_actual, forestMarginal_root_free]

theorem root_child_correlation_square (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) :
    (correlationMatrix (hardCoreLaw A.root.graph activity ha) none (some v))^2 =
      downwardOccupation A activity * (1-downwardOccupation A activity) *
        (parentEffect A (fun v => activity (some v)) (fun v => ha (some v)) v)^2 /
        occupationVariance (hardCoreLaw A.root.graph activity ha) (some v) := by
  have hr := hardCore_occupation_variance_pos A.root.graph activity ha none
  have hv := hardCore_occupation_variance_pos A.root.graph activity ha (some v)
  change 0 < occupationVariance (hardCoreLaw A.root.graph activity ha) none at hr
  change 0 < occupationVariance (hardCoreLaw A.root.graph activity ha) (some v) at hv
  unfold correlationMatrix
  rw [div_pow, Real.sq_sqrt (mul_nonneg hr.le hv.le), root_child_covariance,
    root_occupationVariance] at *
  field_simp

theorem root_child_correlation_square_lower (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) :
    4 * (downwardOccupation A activity * (1-downwardOccupation A activity)) *
        (parentEffect A (fun v => activity (some v)) (fun v => ha (some v)) v)^2 ≤
      (correlationMatrix (hardCoreLaw A.root.graph activity ha) none (some v))^2 := by
  rw [root_child_correlation_square]
  apply (le_div_iff₀ (hardCore_occupation_variance_pos _ _ ha (some v))).mpr
  have hv := occupationVariance_le_quarter (hardCoreLaw A.root.graph activity ha) (some v)
  have hr := hardCore_occupation_variance_pos A.root.graph activity ha none
  change 0 < occupationVariance (hardCoreLaw A.root.graph activity ha) none at hr
  rw [root_occupationVariance] at hr
  have ht := mul_nonneg hr.le (sq_nonneg (parentEffect A (fun v => activity (some v))
    (fun v => ha (some v)) v))
  have hm := mul_le_mul_of_nonneg_left hv ht
  unfold occupationVariance at hm
  nlinarith

/-- Every finite-depth response gives a lower bound on a row norm of the genuine correlation matrix. -/
theorem correlation_row_energy_lower (h : ℕ) (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) :
    4 * (downwardOccupation A activity * (1-downwardOccupation A activity)) *
      responseEnergy h A (fun v => activity (some v)) (fun v => ha (some v)) ≤
        ∑ v, (correlationMatrix (hardCoreLaw A.root.graph activity ha) none v)^2 := by
  rw [Fintype.sum_option]
  apply le_trans _ (le_add_of_nonneg_left (sq_nonneg _))
  unfold responseEnergy
  rw [mul_sum]
  apply sum_le_sum
  intro v _
  split_ifs
  · exact root_child_correlation_square_lower A activity ha v
  · simpa using sq_nonneg (correlationMatrix (hardCoreLaw A.root.graph activity ha) none (some v))

end HardCoreActivityThreshold
