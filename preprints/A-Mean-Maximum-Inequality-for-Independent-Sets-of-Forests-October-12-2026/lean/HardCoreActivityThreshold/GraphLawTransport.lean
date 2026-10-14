import HardCoreActivityThreshold.BooleanConfigurations
import HardCoreActivityThreshold.WeightedForest
import HardCoreActivityThreshold.CorrelationQuadratic

/-! Actual hard-core probabilities and correlations are invariant under graph isomorphism. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
theorem configurationWeight_iso (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (activity : W → ℝ) (s : Finset V) :
    configurationWeight H activity (e.toEquiv.finsetCongr s) =
      configurationWeight G (fun v => activity (e v)) s := by
  unfold configurationWeight
  rw [Equiv.finsetCongr_apply, independent_map_iff G H e.toEquiv.toEmbedding (fun _ _ => e.map_adj_iff.symm)]
  split_ifs
  · exact prod_map _ _ _
  · rfl

omit [DecidableEq V] [DecidableEq W] in
theorem partitionFunction_iso (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (activity : W → ℝ) : partitionFunction G (fun v => activity (e v)) = partitionFunction H activity := by
  unfold partitionFunction
  apply Fintype.sum_equiv e.toEquiv.finsetCongr
  intro s
  exact (configurationWeight_iso G H e activity s).symm

omit [DecidableEq V] [DecidableEq W] in
theorem hardCoreLaw_iso_mass (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (activity : W → ℝ) (ha : ∀ v, 0 < activity v) (s : Finset V) :
    (hardCoreLaw H activity ha).mass (e.toEquiv.finsetCongr s) =
      (hardCoreLaw G (fun v => activity (e v)) (fun v => ha (e v))).mass s := by
  rw [hardCoreLaw_mass, hardCoreLaw_mass, configurationWeight_iso G H e,
    partitionFunction_iso G H e]

omit [DecidableEq V] [DecidableEq W] in
theorem hardCoreLaw_iso_expectation (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (activity : W → ℝ) (ha : ∀ v, 0 < activity v) (f : Finset W → ℝ) :
    (hardCoreLaw H activity ha).expectation f =
      (hardCoreLaw G (fun v => activity (e v)) (fun v => ha (e v))).expectation
        (fun s => f (e.toEquiv.finsetCongr s)) := by
  unfold FiniteLaw.expectation
  symm
  apply Fintype.sum_equiv e.toEquiv.finsetCongr
  intro s
  rw [hardCoreLaw_iso_mass G H e]

omit [Fintype V] [Fintype W] in
@[simp] theorem occupation_finsetCongr (e : V ≃ W) (v : V) (s : Finset V) :
    occupation (e v) (e.finsetCongr s) = occupation v s := by
  simp [occupation, Equiv.finsetCongr_apply]

theorem hardCoreLaw_iso_marginal (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (activity : W → ℝ) (ha : ∀ v, 0 < activity v) (v : V) :
    marginal (hardCoreLaw H activity ha) (e v) =
      marginal (hardCoreLaw G (fun v => activity (e v)) (fun v => ha (e v))) v := by
  unfold marginal
  rw [hardCoreLaw_iso_expectation G H e]
  apply congrArg (FiniteLaw.expectation _)
  funext s
  exact occupation_finsetCongr e.toEquiv v s

theorem hardCoreLaw_iso_variance (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (activity : W → ℝ) (ha : ∀ v, 0 < activity v) (v : V) :
    occupationVariance (hardCoreLaw H activity ha) (e v) =
      occupationVariance (hardCoreLaw G (fun v => activity (e v)) (fun v => ha (e v))) v := by
  simp only [occupationVariance, occupation_variance, hardCoreLaw_iso_marginal G H e]

theorem hardCoreLaw_iso_covariance (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (activity : W → ℝ) (ha : ∀ v, 0 < activity v) (u v : V) :
    occupationCovariance (hardCoreLaw H activity ha) (e u) (e v) =
      occupationCovariance (hardCoreLaw G (fun v => activity (e v)) (fun v => ha (e v))) u v := by
  unfold occupationCovariance
  rw [FiniteLaw.covariance_eq_mixed_moment, FiniteLaw.covariance_eq_mixed_moment]
  change _ - marginal _ (e u) * marginal _ (e v) = _ - marginal _ u * marginal _ v
  rw [hardCoreLaw_iso_marginal G H e, hardCoreLaw_iso_marginal G H e,
    hardCoreLaw_iso_expectation G H e]
  congr 1
  apply congrArg (FiniteLaw.expectation _)
  funext s
  exact congrArg₂ (fun a b : ℝ => a*b) (occupation_finsetCongr e.toEquiv u s)
    (occupation_finsetCongr e.toEquiv v s)

theorem hardCoreLaw_iso_correlation (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (activity : W → ℝ) (ha : ∀ v, 0 < activity v) (u v : V) :
    correlationMatrix (hardCoreLaw H activity ha) (e u) (e v) =
      correlationMatrix (hardCoreLaw G (fun v => activity (e v)) (fun v => ha (e v))) u v := by
  simp only [correlationMatrix, hardCoreLaw_iso_covariance G H e, hardCoreLaw_iso_variance G H e]

theorem hardCoreLaw_iso_quadratic (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (activity : W → ℝ) (ha : ∀ v, 0 < activity v) (c : W → ℝ) :
    (∑ u, ∑ v, c u * correlationMatrix (hardCoreLaw H activity ha) u v * c v) =
      ∑ u, ∑ v, c (e u) * correlationMatrix
        (hardCoreLaw G (fun v => activity (e v)) (fun v => ha (e v))) u v * c (e v) := by
  symm
  apply Fintype.sum_equiv e.toEquiv
  intro u
  apply Fintype.sum_equiv e.toEquiv
  intro v
  change c (e u) * correlationMatrix (hardCoreLaw G (fun v => activity (e v)) (fun v => ha (e v))) u v * c (e v) =
    c (e u) * correlationMatrix (hardCoreLaw H activity ha) (e u) (e v) * c (e v)
  rw [hardCoreLaw_iso_correlation G H e]

end HardCoreActivityThreshold
