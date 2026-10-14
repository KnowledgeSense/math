import HardCoreActivityThreshold.SubcriticalForest
import HardCoreActivityThreshold.GraphLawTransport
import HardCoreActivityThreshold.Forest.ForestRepresentation

/-! The correlation theorem for arbitrary finite forests, without any degree bound. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

theorem subcritical_graph_correlation (Λ : ℝ) (hΛ : 0 < Λ) (hL : Λ < criticalActivity) :
    ∃ C : ℝ, 0 < C ∧ ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V), G.IsAcyclic → ∀ (activity : V → ℝ) (ha : ∀ v, 0 < activity v),
      (∀ v, activity v ≤ Λ) → CorrelationBound (hardCoreLaw G activity ha) C := by
  obtain ⟨C, hC, hc⟩ := subcritical_forest_correlation Λ hΛ hL
  refine ⟨C, hC, ?_⟩
  intro V _ _ G hG activity ha hcap c
  obtain ⟨A, ⟨e⟩⟩ := finite_forest_representation G hG
  have he := hc A (fun v => activity (e v)) (fun v => ha (e v)) (fun v => hcap (e v)) (fun v => c (e v))
  rw [hardCoreLaw_iso_quadratic A.graph G e activity ha c]
  have hs : (∑ v : A.Vertex, c (e v)^2) = ∑ v : V, c v^2 := e.toEquiv.sum_comp (fun v => c v^2)
  rw [hs] at he
  exact he

end HardCoreActivityThreshold
