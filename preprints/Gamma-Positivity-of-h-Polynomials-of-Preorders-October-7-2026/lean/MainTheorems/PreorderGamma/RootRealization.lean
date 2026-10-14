import MainTheorems.PreorderGamma.RootHStar
import MainTheorems.PreorderGamma.SimplicialRealization

namespace ResearchMain.PreorderGamma

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem preorder_root_hStar_simplicial_realization :
    ∃ height : SimplicialRealization.QuotientIndex E → ℝ, (∀ v, 0 < height v) ∧
      Module.finrank ℝ
        (affineSpan ℝ (SimplicialRealization.projectivePolytope height)).direction =
          Fintype.card E ∧
      SimplicialRealization.HasSimplicialBoundary height ∧
      (SimplicialRealization.boundaryHPolynomial height).map (Int.castRingHom ℚ) =
        rootHStar (E := E) := by
  obtain ⟨height, hheight, hdim, hsimp, hh⟩ :=
    preorder_support_simplicial_realization (E := E)
  refine ⟨height, hheight, hdim, hsimp, ?_⟩
  rw [hh, root_hStar_support]
  ext k
  simp [Polynomial.coeff_map]

end ResearchMain.PreorderGamma
