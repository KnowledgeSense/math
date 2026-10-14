import MeanMaximumForests.HubLimits
import MeanMaximumForests.ForestOrderBound
import MeanMaximumForests.GraphRelabeling

namespace MeanMaximumForests
open Filter
open scoped Topology

/-- Every nonempty finite forest is approximated in mean/maximum ratio by actual
trees of every positive order. This is the hub part of the paper's limit proof. -/
theorem exists_all_order_tree_approximation {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ H : ℕ → ForestExpr,
      (∀ n, (H n).graph.IsTree) ∧
      (∀ n, 0 < n → Fintype.card (H n).Vertex = n) ∧
      Tendsto (fun n => graphMean (H n).graph / (H n).graph.indepNum)
        atTop (𝓝 (graphMean G / G.indepNum)) := by
  classical
  obtain ⟨rs, A, hA⟩ := exists_forestRealization G hG Finset.univ
  have hs : 0 < A.statistics.vertices := by
    rw [← hA.card_statistics G, Finset.card_univ]
    exact Fintype.card_pos
  have ha := A.alpha_pos_of_order_pos hs
  have he : A.mean = graphMean G := by
    unfold ForestExpr.mean graphMean meanIndependentSetSize
    rw [hA.count_statistics G, hA.sizeSum_statistics G]
  have heα : A.statistics.alpha = G.indepNum := by
    rw [← hA.alpha_statistics G, independenceNumber_univ]
  refine ⟨HubTrees.allOrders A, HubTrees.allOrders_isTree A, HubTrees.allOrders_card A, ?_⟩
  simpa only [he, heα] using HubTrees.allOrders_ratio_tendsto A hs ha

/-- In the canonical vertex set used by the peak minima, the hub construction
approximates the ratio of any fixed nonempty finite forest at all sufficiently large orders. -/
theorem eventually_exists_tree_ratio_lt {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) (a : ℝ)
    (ha : graphMean G / G.indepNum < a) :
    ∀ᶠ n in atTop, ∃ H : SimpleGraph (Fin n), H.IsTree ∧ graphMean H / H.indepNum < a := by
  classical
  obtain ⟨H, ht, hc, hl⟩ := exists_all_order_tree_approximation G hG
  have he := hl.eventually (gt_mem_nhds ha)
  filter_upwards [he, eventually_gt_atTop 0] with n hn hn0
  let e : (H n).Vertex ≃ Fin n := Fintype.equivFinOfCardEq (hc n hn0)
  let K := (H n).graph.comap e.symm
  let f : K ≃g (H n).graph := SimpleGraph.Iso.comap e.symm (H n).graph
  refine ⟨K, f.isTree_iff.mpr (ht n), ?_⟩
  rwa [graphMean_iso f, indepNum_iso f] at hn

end MeanMaximumForests
