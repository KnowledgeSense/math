import HardCoreActivityThreshold.CompleteSpectralIndependence
import HardCoreActivityThreshold.SubcriticalGap
import HardCoreActivityThreshold.SupportHeatBath

/-! The complete subcritical assertion of the frozen October 12 theorem. -/
namespace HardCoreActivityThreshold

/-- Part (a): constants depend only on the strict activity cap, uniformly over all finite forests,
all positive heterogeneous activities below that cap, and all fields and feasible pinnings. -/
theorem main_a (Λ : ℝ) (hΛ : 0 < Λ) (hL : Λ < criticalActivity) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
        (G : SimpleGraph V), G.IsAcyclic → ∀ (activity : V → ℝ) (ha : ∀ v, 0 < activity v),
        (∀ v, activity v ≤ Λ) →
        CompletelySpectrallyIndependent (hardCoreLaw G activity ha) η ∧
          c / Fintype.card V ≤ heatBathGap (hardCoreLaw G activity ha) := by
  obtain ⟨η, hη, hsi⟩ := subcritical_complete_spectral_independence Λ hΛ hL
  obtain ⟨c, hc, hgap⟩ := subcritical_forest_heatBathGap_lower_of_pos Λ hΛ hL
  exact ⟨η, c, hη, hc, fun G hG activity ha hcap =>
    ⟨hsi G hG activity ha hcap, hgap G hG activity ha hcap⟩⟩

end HardCoreActivityThreshold
