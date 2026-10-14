import HardCoreActivityThreshold.ForestPropagation
import HardCoreActivityThreshold.Correlation

/-! Root correlations of the actual finite hard-core model, derived from its conditional laws. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

@[simp] theorem boolOccupation_configurationEquiv {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (s : Finset V) : boolOccupation v (configurationEquiv s) = occupation v s := by
  simp [boolOccupation, configurationEquiv, occupation]

theorem forest_free_expectation_actual (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (f : (A.Vertex → Bool) → ℝ) :
    (forestLaw A activity ha false).expectation f =
      (hardCoreLaw A.graph activity ha).expectation (fun s => f (configurationEquiv s)) := by
  rw [forestLaw_free]
  exact FiniteLaw.mapEquiv_expectation _ _ _

theorem forestMarginal_free_actual (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) :
    forestMarginal A activity ha false v = marginal (hardCoreLaw A.graph activity ha) v := by
  unfold forestMarginal
  rw [forest_free_expectation_actual]
  simp only [boolOccupation_configurationEquiv, marginal]

theorem root_child_mixed_moment (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) :
    (hardCoreLaw A.root.graph activity ha).expectation (fun s => occupation none s * occupation (some v) s) =
      downwardOccupation A activity *
        forestMarginal A (fun v => activity (some v)) (fun v => ha (some v)) true v := by
  have h := forestLaw_root_free_expectation A activity ha
    (fun x => boolOccupation none x * boolOccupation (some v) x)
  rw [forest_free_expectation_actual] at h
  simp only [boolOccupation_configurationEquiv] at h
  simp [boolOccupation] at h
  unfold forestMarginal
  convert h using 1
  congr 2

theorem root_child_covariance (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) :
    occupationCovariance (hardCoreLaw A.root.graph activity ha) none (some v) =
      downwardOccupation A activity * (1 - downwardOccupation A activity) *
        parentEffect A (fun v => activity (some v)) (fun v => ha (some v)) v := by
  unfold occupationCovariance
  rw [FiniteLaw.covariance_eq_mixed_moment, root_child_mixed_moment]
  change _ - marginal _ none * marginal _ (some v) = _
  rw [← forestMarginal_free_actual, ← forestMarginal_free_actual,
    forestMarginal_root_free, forestMarginal_child_free]
  unfold parentEffect
  ring

theorem stationary_core_marginal (p : ℝ) (hp : 0 ≤ p) (A : ForestExpr)
    (activity : A.root.Vertex → ℝ) (ha : ∀ v, 0 < activity v)
    (hroot : downwardOccupation A activity = stationaryOccupation p)
    (hreg : RegularMessages p A (fun v => activity (some v))) (v : A.root.Vertex) :
    marginal (hardCoreLaw A.root.graph activity ha) v = stationaryOccupation p := by
  rw [← forestMarginal_free_actual]
  cases v with
  | none => rw [forestMarginal_root_free, hroot]
  | some v =>
    rw [forestMarginal_child_free, hroot]
    have h := regular_stationary_marginal p hp A (fun v => activity (some v))
      (fun v => ha (some v)) hreg v
    unfold parentEffect at h
    nlinarith

/-- Exact stationary-core root correlation, for an actual finite weighted hard-core tree. -/
theorem stationary_core_root_correlation (p : ℝ) (hp : 0 < p) (A : ForestExpr)
    (activity : A.root.Vertex → ℝ) (ha : ∀ v, 0 < activity v)
    (hroot : downwardOccupation A activity = stationaryOccupation p)
    (hreg : RegularMessages p A (fun v => activity (some v))) (v : A.root.Vertex) :
    correlationMatrix (hardCoreLaw A.root.graph activity ha) none v = (-p) ^ (A.root.depth v) := by
  cases v with
  | none =>
    rw [correlationMatrix_diag _ _ (hardCore_occupation_variance_pos _ _ ha _)]
    simp [ForestExpr.depth]
  | some v =>
    have hm : 0 < stationaryOccupation p := div_pos hp (by positivity)
    have hm1 : stationaryOccupation p < 1 := by
      unfold stationaryOccupation
      apply (div_lt_one (by positivity : 0 < 1+p)).mpr
      linarith
    have hv : 0 < stationaryOccupation p * (1 - stationaryOccupation p) := mul_pos hm (by linarith)
    unfold correlationMatrix
    rw [root_child_covariance, hroot, regular_parentEffect _ _ _ _ hreg]
    simp only [occupationVariance, occupation_variance,
      stationary_core_marginal p hp.le A activity ha hroot hreg]
    rw [Real.sqrt_mul_self (le_of_lt hv)]
    simp only [ForestExpr.depth]
    exact mul_div_cancel_left₀ _ (ne_of_gt hv)

end HardCoreActivityThreshold
