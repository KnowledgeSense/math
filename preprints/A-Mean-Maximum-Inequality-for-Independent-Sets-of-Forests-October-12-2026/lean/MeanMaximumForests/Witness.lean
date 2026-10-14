import MeanMaximumForests.GraphConstruction
import MeanMaximumForests.WitnessStatistics

namespace MeanMaximumForests.Witness

/-- The witness is an actual finite tree. -/
theorem graph_isTree : tree.graph.IsTree := by
  change (ForestExpr.root _).graph.IsTree
  exact ForestExpr.root_graph_isTree _

theorem graph_vertex_count : Fintype.card tree.Vertex = 71308 := by
  rw [tree.graph_card_statistics, vertex_count]

theorem graph_independence_number : tree.graph.indepNum = 48619 := by
  rw [tree.graph_indepNum_statistics, independence_number]

/-- The exact graph-theoretic upper witness, with a kernel-checked strict rational comparison. -/
theorem graph_ratio_lt : graphMean tree.graph / tree.graph.indepNum < (473403 / 1000000 : ℝ) := by
  have hc : (0 : ℝ) < tree.statistics.count := by
    rw [← tree.graph_count_statistics]
    exact Nat.cast_pos.mpr (independentSetCount_pos tree.graph _)
  have ha : (0 : ℝ) < tree.statistics.alpha := by rw [independence_number]; norm_num
  rw [tree.graphMean_statistics, tree.graph_indepNum_statistics, div_div]
  apply (div_lt_div_iff₀ (mul_pos hc ha) (by norm_num : (0 : ℝ) < 1000000)).mpr
  have h : (1000000 : ℝ) * tree.statistics.sizeSum <
      473403 * tree.statistics.alpha * tree.statistics.count := by exact_mod_cast strict_upper_bound
  nlinarith

end MeanMaximumForests.Witness
