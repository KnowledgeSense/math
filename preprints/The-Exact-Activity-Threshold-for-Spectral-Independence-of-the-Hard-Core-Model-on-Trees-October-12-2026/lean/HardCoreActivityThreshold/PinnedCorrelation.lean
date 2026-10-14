import HardCoreActivityThreshold.SubcriticalGraph
import HardCoreActivityThreshold.WithinGraphTransport
import HardCoreActivityThreshold.PinnedForestTensorization
import HardCoreActivityThreshold.CorrelationFlip
import HardCoreActivityThreshold.Fields

/-! The correlation bound persists under every feasible pinning and every activity decrease. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem subcritical_pinned_field_correlation (Λ : ℝ) (hΛ : 0 < Λ) (hL : Λ < criticalActivity) :
    ∃ C : ℝ, 0 < C ∧ ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V), G.IsAcyclic → ∀ (activity : V → ℝ) (ha : ∀ v, 0 < activity v),
      (∀ v, activity v ≤ Λ) → ∀ (field : V → ℝ) (hf : ∀ v, 0 < field v),
      (∀ v, field v ≤ 1) → ∀ (pinned occupied : Finset V)
      (hp : 0 < (applyField (hardCoreLaw G activity ha) field hf).eventMass (agreesWith pinned occupied)),
      CorrelationBound ((applyField (hardCoreLaw G activity ha) field hf).condition
        (agreesWith pinned occupied) hp) C := by
  obtain ⟨C, hC, hc⟩ := subcritical_graph_correlation Λ hΛ hL
  refine ⟨C, hC, ?_⟩
  intro V _ _ G hG activity ha hcap field hf hfield pinned occupied hp
  simp only [applyField_hardCore] at hp ⊢
  change CorrelationBound (pinnedHardCoreLaw G (fun v => activity v*field v)
    (fun v => mul_pos (ha v) (hf v)) pinned occupied hp) C
  rw [pinnedHardCoreLaw_eq_flip_within]
  apply CorrelationBound.mapEquiv_configurationFlip
  apply hardCoreWithin_correlationBound _ _ _ _ hC.le
  apply hc _ (hG.induce _)
  intro v
  exact (mul_le_of_le_one_right (ha v.val).le (hfield v.val)).trans (hcap v.val)

end HardCoreActivityThreshold
