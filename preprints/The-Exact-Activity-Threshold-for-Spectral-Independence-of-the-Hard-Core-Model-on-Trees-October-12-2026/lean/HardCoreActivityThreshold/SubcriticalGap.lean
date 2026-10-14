import HardCoreActivityThreshold.ForestGapLower
import HardCoreActivityThreshold.PinnedCorrelation

/-! The complete uniform lower heat-bath gap for subcritical hard-core laws on finite forests. -/
namespace HardCoreActivityThreshold

/-- The constant depends only on the activity cap. Both the low-field tensorization and
its finite revealing boost are proved, for the actual normalized hard-core law. -/
theorem subcritical_forest_heatBathGap_lower_of_pos (Λ : ℝ)
    (hΛ : 0 < Λ) (hL : Λ < criticalActivity) :
    ∃ c : ℝ, 0 < c ∧ ∀ {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V), G.IsAcyclic → ∀ (activity : V → ℝ) (ha : ∀ v, 0 < activity v),
      (∀ v, activity v ≤ Λ) → c / Fintype.card V ≤ heatBathGap (hardCoreLaw G activity ha) := by
  obtain ⟨B, _, hcorr⟩ := subcritical_pinned_field_correlation Λ hΛ hL
  refine ⟨boostedForestGapConstant Λ B, boostedForestGapConstant_pos Λ B, ?_⟩
  intro V _ _ _ G hG activity ha hcap
  apply hardCore_forest_gap_of_field_correlation G hG activity ha hcap
  intro x hx hx1 r hr
  exact hcorr G hG activity ha hcap (fun _ => x) (fun _ => hx) (fun _ => hx1) r r hr

/-- The spectral-gap assertion of the lower-threshold theorem, without a degree bound.
For nonpositive caps there is no positive-activity law on a nonempty vertex set. -/
theorem subcritical_forest_heatBathGap_lower (Λ : ℝ) (hL : Λ < criticalActivity) :
    ∃ c : ℝ, 0 < c ∧ ∀ {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V), G.IsAcyclic → ∀ (activity : V → ℝ) (ha : ∀ v, 0 < activity v),
      (∀ v, activity v ≤ Λ) → c / Fintype.card V ≤ heatBathGap (hardCoreLaw G activity ha) := by
  by_cases hΛ : 0 < Λ
  · exact subcritical_forest_heatBathGap_lower_of_pos Λ hΛ hL
  · refine ⟨1, zero_lt_one, ?_⟩
    intro V _ _ _ _ _ activity ha hcap
    have hv := ha (Classical.ofNonempty : V)
    have hc := hcap (Classical.ofNonempty : V)
    exact (hΛ (lt_of_lt_of_le hv hc)).elim

end HardCoreActivityThreshold
