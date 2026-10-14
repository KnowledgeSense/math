import MeanMaximumForests.PeakAnalysis.ForestSparse
import MeanMaximumForests.PeakAnalysis.BipartitePairs

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable

/-- Every finite forest has a genuine bipartition whose first side contains many low-degree vertices. -/
theorem forest_good_bipartition {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ L R : Finset V, Independent G L ∧ Independent G R ∧ Disjoint L R ∧ L ∪ R = univ ∧
      Fintype.card V ≤ 4 * (L.filter (fun v => G.degree v ≤ 3)).card := by
  classical
  obtain ⟨c, b, hcard⟩ := forest_low_degree_color_class G hG
  let L := univ.filter (fun v => c v = b)
  let R := univ.filter (fun v => c v ≠ b)
  have hL : Independent G L := by
    intro u hu v hv hadj
    exact c.valid hadj ((mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm)
  have hR : Independent G R := by
    intro u hu v hv hadj
    have hone : ∀ x y b : Fin 2, x ≠ b → y ≠ b → x = y := by decide
    exact c.valid hadj (hone (c u) (c v) b (mem_filter.mp hu).2 (mem_filter.mp hv).2)
  have hd : Disjoint L R := by
    apply disjoint_left.mpr
    intro v hvL hvR
    exact (mem_filter.mp hvR).2 (mem_filter.mp hvL).2
  have hc : L ∪ R = univ := by ext v; simp [L, R]; tauto
  refine ⟨L, R, hL, hR, hd, hc, ?_⟩
  simpa only [L, filter_filter, and_comm] using hcard

end MeanMaximumForests.PeakAnalysis
