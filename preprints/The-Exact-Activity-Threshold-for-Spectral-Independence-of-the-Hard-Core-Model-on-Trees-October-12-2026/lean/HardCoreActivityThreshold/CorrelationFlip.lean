import HardCoreActivityThreshold.CoordinateFlip
import HardCoreActivityThreshold.CovarianceResponse

/-! Correlation quadratic bounds are invariant under coordinatewise occupied/vacant relabeling. -/
namespace HardCoreActivityThreshold
open Finset
open scoped symmDiff
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem occupation_configurationFlip (occupied : Finset V) (v : V) (s : Finset V) :
    occupation v (configurationFlip occupied s) =
      if v ∈ occupied then 1 - occupation v s else occupation v s := by
  by_cases ho : v ∈ occupied <;> by_cases hs : v ∈ s <;>
    simp [occupation, configurationFlip, mem_symmDiff, ho, hs]

theorem marginal_configurationFlip (μ : FiniteLaw (Finset V)) (occupied : Finset V) (v : V) :
    marginal (μ.mapEquiv (configurationFlip occupied)) v =
      if v ∈ occupied then 1 - marginal μ v else marginal μ v := by
  unfold marginal
  rw [FiniteLaw.mapEquiv_expectation]
  simp only [occupation_configurationFlip]
  by_cases ho : v ∈ occupied
  · simp only [ho, ite_true]
    rw [μ.expectation_sub, μ.expectation_const]
  · simp only [ho, ite_false]

theorem occupationVariance_configurationFlip (μ : FiniteLaw (Finset V))
    (occupied : Finset V) (v : V) :
    occupationVariance (μ.mapEquiv (configurationFlip occupied)) v = occupationVariance μ v := by
  unfold occupationVariance
  rw [occupation_variance, occupation_variance, marginal_configurationFlip]
  by_cases ho : v ∈ occupied
  · simp only [ho, ite_true]
    ring
  · simp only [ho, ite_false]

theorem normalizedOccupation_configurationFlip (μ : FiniteLaw (Finset V))
    (occupied : Finset V) (v : V) (s : Finset V) :
    normalizedOccupation (μ.mapEquiv (configurationFlip occupied)) v (configurationFlip occupied s) =
      if v ∈ occupied then -normalizedOccupation μ v s else normalizedOccupation μ v s := by
  unfold normalizedOccupation
  rw [occupation_configurationFlip, marginal_configurationFlip, occupationVariance_configurationFlip]
  by_cases ho : v ∈ occupied
  · simp only [ho, ite_true]
    ring
  · simp only [ho, ite_false]

/-- Deterministic coordinates are included; no nonzero-variance assumption is required. -/
theorem CorrelationBound.mapEquiv_configurationFlip {μ : FiniteLaw (Finset V)} {C : ℝ}
    (h : CorrelationBound μ C) (occupied : Finset V) :
    CorrelationBound (μ.mapEquiv (configurationFlip occupied)) C := by
  intro a
  rw [correlation_quadratic_variance, FiniteLaw.mapEquiv_variance]
  have he : (fun s => linearOccupation (μ.mapEquiv (configurationFlip occupied)) a
        (configurationFlip occupied s)) =
      linearOccupation μ (fun v => if v ∈ occupied then -a v else a v) := by
    funext s
    unfold linearOccupation
    apply sum_congr rfl
    intro v _
    rw [normalizedOccupation_configurationFlip]
    by_cases ho : v ∈ occupied <;> simp [ho]
  rw [he, ← correlation_quadratic_variance]
  simpa only [ite_pow, neg_sq, ite_self] using
    h (fun v => if v ∈ occupied then -a v else a v)

end HardCoreActivityThreshold
