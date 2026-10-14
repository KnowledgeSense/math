import HardCoreActivityThreshold.Forest.ForestRepresentation
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold HardCoreActivityThreshold.Forest Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem forest_edge_count_le (G : SimpleGraph V) (hG : G.IsAcyclic) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  obtain ⟨A, ⟨e⟩⟩ := finite_forest_representation G hG
  rw [← e.card_edgeFinset_eq, ← Fintype.card_congr e.toEquiv]
  let f : A.Vertex ↪ A.root.Vertex := ⟨Option.some, Option.some_injective _⟩
  have hmap : A.graph.map f ≤ A.root.graph :=
    map_le_iff_le_comap.mpr (fun _ _ h => h)
  have hc := card_le_card (edgeFinset_mono hmap)
  rw [card_edgeFinset_map] at hc
  have ht := A.root_graph_isTree.card_edgeFinset
  simp only [ForestExpr.Vertex, Fintype.card_option] at ht
  omega

theorem forest_degree_sum_le (G : SimpleGraph V) (hG : G.IsAcyclic) :
    (∑ v, G.degree v) ≤ 2 * Fintype.card V := by
  classical
  rw [G.sum_degrees_eq_twice_card_edges]
  exact Nat.mul_le_mul_left 2 (forest_edge_count_le G hG)

theorem forest_many_low_degree (G : SimpleGraph V) (hG : G.IsAcyclic) :
    Fintype.card V ≤ 2 * (univ.filter (fun v => G.degree v ≤ 3)).card := by
  classical
  let D := univ.filter (fun v => G.degree v ≤ 3)
  let E := univ.filter (fun v => ¬ G.degree v ≤ 3)
  have hcards : D.card + E.card = Fintype.card V := by
    exact (card_filter_add_card_filter_not (s := univ) (fun v => G.degree v ≤ 3)).trans (card_univ)
  have hsum : 4 * E.card ≤ ∑ v ∈ E, G.degree v := by
    have h := sum_le_sum (s := E) (f := fun _ => 4) (g := fun v => G.degree v) (fun v hv => by
      have hh := (mem_filter.mp hv).2
      omega)
    simpa only [sum_const, smul_eq_mul, mul_comm] using h
  have hsum' : (∑ v ∈ E, G.degree v) ≤ ∑ v, G.degree v :=
    sum_le_sum_of_subset_of_nonneg (subset_univ E) (fun _ _ _ => Nat.zero_le _)
  have hdeg := forest_degree_sum_le G hG
  change Fintype.card V ≤ 2 * D.card
  omega

/-- One color class contains at least one quarter of all vertices with degree at most three. -/
theorem forest_low_degree_color_class (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ c : G.Coloring (Fin 2), ∃ b : Fin 2,
      Fintype.card V ≤ 4 * (univ.filter (fun v => G.degree v ≤ 3 ∧ c v = b)).card := by
  classical
  let c := hG.coloringTwo
  let D := univ.filter (fun v => G.degree v ≤ 3)
  let L := D.filter (fun v => c v = 0)
  let R := D.filter (fun v => c v = 1)
  have he : R = D.filter (fun v => ¬ c v = 0) := by
    ext v
    simp only [R, mem_filter]
    have hc : (c v).val < 2 := (c v).isLt
    have hcv : (c v).val = 0 ∨ (c v).val = 1 := by omega
    have hcv' : c v = 0 ∨ c v = 1 := hcv.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
    rcases hcv' with h | h <;> simp [h]
  have hcards : L.card + R.card = D.card := by
    rw [he]
    exact card_filter_add_card_filter_not (s := D) (fun v => c v = 0)
  have hlow := forest_many_low_degree G hG
  change Fintype.card V ≤ 2 * D.card at hlow
  by_cases h : L.card ≤ R.card
  · refine ⟨c, 1, ?_⟩
    have hn : Fintype.card V ≤ 4 * R.card := by omega
    simpa only [R, D, filter_filter] using hn
  · refine ⟨c, 0, ?_⟩
    have hn : Fintype.card V ≤ 4 * L.card := by omega
    simpa only [L, D, filter_filter] using hn

end MeanMaximumForests.PeakAnalysis
