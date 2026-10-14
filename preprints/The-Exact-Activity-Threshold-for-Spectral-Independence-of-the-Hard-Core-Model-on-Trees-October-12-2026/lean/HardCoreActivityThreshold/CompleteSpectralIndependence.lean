import HardCoreActivityThreshold.PinnedCorrelation
import HardCoreActivityThreshold.CorrelationSignability
import HardCoreActivityThreshold.DegenerateInfluence
import HardCoreActivityThreshold.GaugeSpectrum
import HardCoreActivityThreshold.MatrixSpectrum

/-! Actual complete spectral independence, including all deterministic pinned coordinates. -/
namespace HardCoreActivityThreshold
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A signable correlation quadratic bound controls the actual conditional influence spectrum. -/
theorem influenceSpectralRadius_le_of_signable (μ : FiniteLaw (Finset V)) (C : ℝ)
    (hC : 0 ≤ C) (hc : CorrelationBound μ C) (hsign : CorrelationSignable μ) :
    influenceSpectralRadius μ ≤ ENNReal.ofReal (C+1) := by
  obtain ⟨s, hs, hpos⟩ := hsign
  have habs : Matrix.of (fun u v => |correlationMatrix μ u v|) =
      Matrix.of (fun u v => s u * correlationMatrix μ u v * s v) := by
    rw [absolute_eq_signGauge s hs _ (by simpa only [signGauge_entry] using hpos)]
    ext u v
    exact signGauge_entry s _ u v
  rw [influenceSpectralRadius_eq_active]
  unfold absoluteActiveCorrelation
  rw [habs]
  apply signed_active_radius_bound _ (correlationMatrix_isHermitian μ) s (varianceActive μ)
    hs (varianceActive_mem μ) C hC
  · intro x
    simpa only [dotProduct, mulVec, mul_sum, mul_assoc] using correlation_quadratic_nonneg μ x
  · intro x
    simpa only [dotProduct, mulVec, mul_sum, mul_assoc] using hc x

/-- Every activity decrease and every feasible partial assignment obey the same radius bound. -/
theorem subcritical_complete_spectral_independence (Λ : ℝ) (hΛ : 0 < Λ)
    (hL : Λ < criticalActivity) :
    ∃ η : ℝ, 0 < η ∧ ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V), G.IsAcyclic → ∀ (activity : V → ℝ) (ha : ∀ v, 0 < activity v),
      (∀ v, activity v ≤ Λ) → CompletelySpectrallyIndependent (hardCoreLaw G activity ha) η := by
  obtain ⟨C, hC, hc⟩ := subcritical_pinned_field_correlation Λ hΛ hL
  refine ⟨C+1, by positivity, ?_⟩
  intro V _ _ G hG activity ha hcap field hf hfield pinned occupied hp
  apply influenceSpectralRadius_le_of_signable _ C hC.le
  · exact hc G hG activity ha hcap field hf hfield pinned occupied hp
  · exact pinned_field_forest_correlation_signable G hG activity ha field hf pinned occupied hp

end HardCoreActivityThreshold
