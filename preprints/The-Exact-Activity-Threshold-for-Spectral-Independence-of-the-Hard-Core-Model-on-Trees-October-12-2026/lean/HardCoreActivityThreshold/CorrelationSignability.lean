import HardCoreActivityThreshold.SignGauge
import HardCoreActivityThreshold.ParentColumnBounds
import HardCoreActivityThreshold.GraphLawTransport
import HardCoreActivityThreshold.Forest.ForestRepresentation
import HardCoreActivityThreshold.WithinGraphTransport
import HardCoreActivityThreshold.PinnedForestTensorization
import HardCoreActivityThreshold.CorrelationFlip
import HardCoreActivityThreshold.Fields

/-! Actual forest correlations admit a sign gauge, including restricted and pinned laws. -/
namespace HardCoreActivityThreshold
open Finset Forest Matrix
attribute [local instance] Classical.propDecidable

theorem parentCorrelationMatrix_nonpos (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (u v : A.Vertex) :
    parentCorrelationMatrix A activity ha u v ≤ 0 := by
  unfold parentCorrelationMatrix
  simp only [Matrix.of_apply]
  split_ifs
  · exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (vertexMessage_mem_Ioo A activity ha u).1.le)
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · rfl

/-- Depth parity signs the actual heterogeneous hard-core correlation matrix on a rooted forest. -/
theorem forest_correlation_signable (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) : CorrelationSignable (forestHC A activity ha) := by
  refine ⟨fun v => (-1 : ℝ)^A.depth v, rank_sign_square A.depth, ?_⟩
  have hfac := nilpotent_triangular_factorization (correlationMatrix (forestHC A activity ha))
    (parentCorrelationMatrix A activity ha) (innovationDiagonal A activity ha) (univ.sup A.depth)
    (parentCorrelationMatrix_nilpotent A activity ha) (forest_correlation_factorization A activity ha)
  have hK := rank_sign_geometric_nonnegative (parentCorrelationMatrix A activity ha) A.depth
    (fun u v huv => forestParent_depth A u v (parentCorrelationMatrix_support A activity ha u v huv))
    (parentCorrelationMatrix_nonpos A activity ha) (univ.sup A.depth)
  have hR := signGauge_factor_nonnegative (fun v => (-1 : ℝ)^A.depth v) (rank_sign_square A.depth)
    _ (innovationDiagonal A activity ha) (innovationDiagonal_nonneg A activity ha) hK
  rw [← hfac] at hR
  simpa only [signGauge_entry] using hR

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every finite acyclic graph has signable actual correlations, for all positive activities. -/
theorem hardCore_forest_correlation_signable (G : SimpleGraph V) (hG : G.IsAcyclic)
    (activity : V → ℝ) (ha : ∀ v, 0 < activity v) :
    CorrelationSignable (hardCoreLaw G activity ha) := by
  obtain ⟨A, ⟨e⟩⟩ := finite_forest_representation G hG
  obtain ⟨s, hs, hR⟩ := forest_correlation_signable A (fun v => activity (e v)) (fun v => ha (e v))
  refine ⟨fun v => s (e.toEquiv.symm v), fun v => hs _, ?_⟩
  intro u v
  obtain ⟨u, rfl⟩ := e.toEquiv.surjective u
  obtain ⟨v, rfl⟩ := e.toEquiv.surjective v
  simp only [Equiv.symm_apply_apply]
  change 0 ≤ s u * correlationMatrix (hardCoreLaw G activity ha) (e u) (e v) * s v
  erw [hardCoreLaw_iso_correlation A.graph G e activity ha]
  exact hR u v

/-- Adjoining deterministic vacant coordinates preserves signability. -/
theorem hardCoreWithin_correlation_signable (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (allowed : Finset V)
    (hc : CorrelationSignable (hardCoreLaw (G.induce (allowed : Set V))
      (fun v => activity v.val) (fun v => ha v.val))) :
    CorrelationSignable (hardCoreWithin G activity ha allowed) := by
  obtain ⟨s, hs, hR⟩ := hc
  let t : V → ℝ := fun v => if hv : v ∈ allowed then s ⟨v, hv⟩ else 1
  refine ⟨t, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ allowed
    · simpa only [t, dite_eq_left hv] using hs ⟨v, hv⟩
    · simp only [t, dite_eq_right hv, mul_one]
  · intro u v
    by_cases hu : u ∈ allowed
    · by_cases hv : v ∈ allowed
      · simp only [t, dite_eq_left hu, dite_eq_left hv]
        rw [hardCoreWithin_correlation_induce G activity ha allowed ⟨u, hu⟩ ⟨v, hv⟩]
        exact hR _ _
      · rw [hardCoreWithin_correlation_outside_right G activity ha allowed u v hv]
        simp
    · rw [correlationMatrix_symm, hardCoreWithin_correlation_outside_right G activity ha allowed v u hu]
      simp

/-- Restricting the allowed vertices of a finite forest preserves actual correlation signs. -/
theorem hardCoreWithin_forest_correlation_signable (G : SimpleGraph V) (hG : G.IsAcyclic)
    (activity : V → ℝ) (ha : ∀ v, 0 < activity v) (allowed : Finset V) :
    CorrelationSignable (hardCoreWithin G activity ha allowed) :=
  hardCoreWithin_correlation_signable G activity ha allowed
    (hardCore_forest_correlation_signable _ (hG.induce _) _ _)

/-- The correlation matrix changes by the corresponding coordinate signs under occupation flips. -/
theorem correlationMatrix_configurationFlip (μ : FiniteLaw (Finset V))
    (occupied : Finset V) (u v : V) :
    correlationMatrix (μ.mapEquiv (configurationFlip occupied)) u v =
      (if u ∈ occupied then (-1 : ℝ) else 1) * correlationMatrix μ u v *
        (if v ∈ occupied then (-1 : ℝ) else 1) := by
  rw [← normalizedOccupation_product, FiniteLaw.mapEquiv_expectation]
  simp only [normalizedOccupation_configurationFlip]
  have he : (fun s => (if u ∈ occupied then -normalizedOccupation μ u s else normalizedOccupation μ u s) *
      (if v ∈ occupied then -normalizedOccupation μ v s else normalizedOccupation μ v s)) =
      (fun s => ((if u ∈ occupied then (-1 : ℝ) else 1) * (if v ∈ occupied then (-1 : ℝ) else 1)) *
        (normalizedOccupation μ u s * normalizedOccupation μ v s)) := by
    funext s
    by_cases hu : u ∈ occupied <;> by_cases hv : v ∈ occupied <;> simp [hu, hv]
  rw [he, FiniteLaw.expectation_smul, normalizedOccupation_product]
  ring

/-- Coordinate flips preserve signability even when some coordinates have zero variance. -/
theorem CorrelationSignable.mapEquiv_configurationFlip {μ : FiniteLaw (Finset V)}
    (h : CorrelationSignable μ) (occupied : Finset V) :
    CorrelationSignable (μ.mapEquiv (configurationFlip occupied)) := by
  obtain ⟨s, hs, hR⟩ := h
  refine ⟨fun v => (if v ∈ occupied then (-1 : ℝ) else 1) * s v, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ occupied <;> simpa [hv] using hs v
  · intro u v
    rw [correlationMatrix_configurationFlip]
    by_cases hu : u ∈ occupied <;> by_cases hv : v ∈ occupied <;> simpa [hu, hv] using hR u v

/-- Feasible occupied/vacant pinning of any positive-activity forest law retains signability. -/
theorem pinnedHardCore_forest_correlation_signable (G : SimpleGraph V) (hG : G.IsAcyclic)
    (activity : V → ℝ) (ha : ∀ v, 0 < activity v) (pinned occupied : Finset V)
    (hp : 0 < (hardCoreLaw G activity ha).eventMass (agreesWith pinned occupied)) :
    CorrelationSignable (pinnedHardCoreLaw G activity ha pinned occupied hp) := by
  rw [pinnedHardCoreLaw_eq_flip_within]
  apply CorrelationSignable.mapEquiv_configurationFlip
  apply hardCoreWithin_correlation_signable
  exact hardCore_forest_correlation_signable _ (hG.induce _) _ _

/-- Positive coordinate fields followed by feasible pinning preserve forest signability. -/
theorem pinned_field_forest_correlation_signable (G : SimpleGraph V) (hG : G.IsAcyclic)
    (activity : V → ℝ) (ha : ∀ v, 0 < activity v) (field : V → ℝ) (hf : ∀ v, 0 < field v)
    (pinned occupied : Finset V)
    (hp : 0 < (applyField (hardCoreLaw G activity ha) field hf).eventMass (agreesWith pinned occupied)) :
    CorrelationSignable ((applyField (hardCoreLaw G activity ha) field hf).condition
      (agreesWith pinned occupied) hp) := by
  simp only [applyField_hardCore] at hp ⊢
  exact pinnedHardCore_forest_correlation_signable G hG _ _ pinned occupied hp

end HardCoreActivityThreshold
