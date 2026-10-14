import SphericalTreeFailures.TuningExistence
import SphericalTreeFailures.HardCoreWeights

namespace SphericalTreeFailures
open Polynomial

theorem excludedPartition_zero (n : ℕ) (activity : ℝ) :
    excludedPartition 0 n activity = pathPartition n activity := rfl

theorem includedPartition_zero_succ (n : ℕ) (activity : ℝ) :
    includedPartition 0 (n + 1) activity = activity * pathPartition n activity := by
  unfold includedPartition totalPartition
  rw [ForestExpr.graph_polynomial]
  simp [sphericalTree, pendantPath, ForestExpr.polynomials, excludedPartition,
    pathPartition, pathPolynomial]

theorem pathPartition_pos (n : ℕ) {activity : ℝ} (ha : 0 < activity) :
    0 < pathPartition n activity := by
  cases n with
  | zero => simp [pathPartition, pathPolynomial_zero]
  | succ n =>
    have h := totalPartition_pos 0 n ha
    unfold totalPartition at h
    rw [ForestExpr.graph_polynomial] at h
    exact h

theorem excludedPartition_pos (m n : ℕ) {activity : ℝ} (ha : 0 < activity) :
    0 < excludedPartition m n activity := by
  cases m with
  | zero => exact pathPartition_pos n ha
  | succ m => rw [excludedPartition_succ]; exact pow_pos (totalPartition_pos m n ha) 2

/-- The root occupation probability is constant at every binary-core depth after tuning. -/
theorem tuned_root_probability (k : ℕ) {r : ℝ} (hr : 0 < r)
    (htune : tunedActivity r * pathPartition (2 * k) (tunedActivity r) =
      r * pathPartition (2 * k + 1) (tunedActivity r)) (m : ℕ) :
    includedPartition m (2 * k + 1) (tunedActivity r) /
      totalPartition m (2 * k + 1) (tunedActivity r) = broadcastParameter r := by
  have hb : includedPartition 0 (2 * k + 1) (tunedActivity r) =
      r * excludedPartition 0 (2 * k + 1) (tunedActivity r) := by
    rw [includedPartition_zero_succ, excludedPartition_zero]
    exact htune
  have hi := tuned_partition_ratio (2 * k + 1) (tunedActivity r) r rfl hb m
  have hz := excludedPartition_pos m (2 * k + 1) (tunedActivity_pos hr)
  have ht : totalPartition m (2 * k + 1) (tunedActivity r) =
      (1 + r) * excludedPartition m (2 * k + 1) (tunedActivity r) := by
    unfold includedPartition at hi
    linarith
  rw [hi, ht]
  unfold broadcastParameter
  have hr1 : 1 + r ≠ 0 := by positivity
  field_simp

end SphericalTreeFailures
