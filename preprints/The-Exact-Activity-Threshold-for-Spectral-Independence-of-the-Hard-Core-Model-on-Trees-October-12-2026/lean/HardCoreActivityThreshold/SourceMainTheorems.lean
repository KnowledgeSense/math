import HardCoreActivityThreshold.SubcriticalTheorem
import HardCoreActivityThreshold.SupercriticalTheorem
import HardCoreActivityThreshold.ReversibleSpectrum
import HardCoreActivityThreshold.HardCoreSupport

/-! The original main assertions with the ordinary support-transition spectral gap. -/
namespace HardCoreActivityThreshold

/-- Part (a), explicitly using one minus the second-largest eigenvalue of the actual
support transition matrix (and its proved one-state convention). -/
theorem main_a_spectral (Λ : ℝ) (hΛ : 0 < Λ) (hL : Λ < criticalActivity) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
        (G : SimpleGraph V), G.IsAcyclic → ∀ (activity : V → ℝ) (ha : ∀ v, 0 < activity v),
        (∀ v, activity v ≤ Λ) →
        CompletelySpectrallyIndependent (hardCoreLaw G activity ha) η ∧
          c / Fintype.card V ≤ (supportHeatBath (hardCoreLaw G activity ha)).ordinarySpectralGap
            (fun s => s.property) := by
  obtain ⟨η, c, hη, hc, hmain⟩ := main_a Λ hΛ hL
  refine ⟨η, c, hη, hc, ?_⟩
  intro V _ _ _ G hG activity ha hcap
  obtain ⟨hsi, hgap⟩ := hmain G hG activity ha hcap
  exact ⟨hsi, by rwa [← heatBathGap_eq_ordinary_support_gap]⟩

/-- Part (b), on unpinned constant-activity trees, with the ordinary transition spectral gap. -/
theorem main_b_spectral (a : ℝ) (ha : criticalActivity ≤ a) (M : ℝ) (hM : 0 < M) :
    ∃ A : Forest.ForestExpr,
      let μ := hardCoreLaw A.root.graph (fun _ => a) (fun _ => lt_of_lt_of_le criticalActivity_pos ha)
      A.root.graph.IsTree ∧ ENNReal.ofReal M ≤ influenceSpectralRadius μ ∧
        (Fintype.card A.root.Vertex : ℝ) *
          (supportHeatBath μ).ordinarySpectralGap (fun s => s.property) ≤ 1/M := by
  obtain ⟨A, htree, hspec, hgap⟩ := main_b a ha M hM
  exact ⟨A, htree, hspec, by rwa [← heatBathGap_eq_ordinary_support_gap]⟩

/-- Nonempty positive-activity hard-core chains always have at least two genuine states,
so their ordinary spectral gap is literally one minus the second sorted transition eigenvalue. -/
theorem hardCore_gap_eq_one_sub_second_eigenvalue {V : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    (activity : V → ℝ) (ha : ∀ v, 0 < activity v) :
    heatBathGap (hardCoreLaw G activity ha) =
      1 - (supportHeatBath (hardCoreLaw G activity ha)).transitionEigenvalues (fun s => s.property)
        ⟨1, lt_of_lt_of_le (by decide : 1 < 2) (hardCore_support_card_ge_two G activity ha)⟩ :=
  heatBathGap_eq_one_sub_second_support_eigenvalue _ _

end HardCoreActivityThreshold
