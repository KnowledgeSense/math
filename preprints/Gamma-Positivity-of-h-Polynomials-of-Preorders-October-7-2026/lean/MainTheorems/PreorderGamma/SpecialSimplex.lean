import MainTheorems.PreorderGamma.GeometricFacets
import MainTheorems.PreorderGamma.RootDimension

namespace ResearchMain.PreorderGamma

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem root_has_special_diagonal_simplex :
    AffineIndependent ℝ (fun i : Option E => rootVertex i i) ∧
      (∀ i : Option E, rootVertex i i ∈ rootPolytope (E := E)) ∧
      Module.finrank ℝ (affineSpan ℝ (rootPolytope (E := E))).direction =
        2 * Fintype.card E ∧
      Module.finrank ℝ
        (affineSpan ℝ (Set.range fun i : Option E => rootVertex i i)).direction =
          Fintype.card E ∧
      ∀ s : Set (RootAmbient E), IsGeometricRootFacet s →
        ∃! i : Option E, rootVertex i i ∉ s := by
  refine ⟨diagonalRootVertices_affineIndependent, ?_, rootPolytope_dimension,
    diagonalRootVertices_dimension, ?_⟩
  · intro i
    exact rootVertex_mem_rootPolytope (diagonalEdge i)
  · intro s hs
    exact geometricRootFacet_unique_missing_diagonal hs

end ResearchMain.PreorderGamma
