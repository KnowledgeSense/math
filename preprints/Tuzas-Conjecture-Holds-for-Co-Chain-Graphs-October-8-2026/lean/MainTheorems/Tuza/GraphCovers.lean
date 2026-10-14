import MainTheorems.Tuza.SumGraph
import MainTheorems.Tuza.SplitClique

namespace ResearchMain.Tuza

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem graph_triangle_cover {G H : SimpleGraph V} [DecidableRel H.Adj]
    (hHG : H ≤ G)
    (h : ∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
      H.Adj x y ∨ H.Adj x z ∨ H.Adj y z) : Cover G H.edgeFinset := by
  refine ⟨?_, ?_⟩
  · intro e he
    exact SimpleGraph.edgeSet_mono hHG (H.mem_edgeFinset.mp he)
  · intro t ht
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := G.is3Clique_iff.mp ht
    rcases h x y z hxy hxz hyz with hh | hh | hh
    · refine ⟨s(x, y), Finset.mem_inter.mpr ⟨?_, H.mem_edgeFinset.mpr hh⟩⟩
      exact mem_triangleEdges.mpr ⟨by simp, by simp, hxy.ne⟩
    · refine ⟨s(x, z), Finset.mem_inter.mpr ⟨?_, H.mem_edgeFinset.mpr hh⟩⟩
      exact mem_triangleEdges.mpr ⟨by simp, by simp, hxz.ne⟩
    · refine ⟨s(y, z), Finset.mem_inter.mpr ⟨?_, H.mem_edgeFinset.mpr hh⟩⟩
      exact mem_triangleEdges.mpr ⟨by simp, by simp, hyz.ne⟩

end ResearchMain.Tuza
