import MainTheorems.PreorderGamma.SimplicialRealization.BoundaryEnumerator
import MainTheorems.PreorderGamma.SimplicialRealization.LowDimension

namespace ResearchMain.PreorderGamma

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem preorder_support_simplicial_realization :
    ∃ height : SimplicialRealization.QuotientIndex E → ℝ, (∀ v, 0 < height v) ∧
      Module.finrank ℝ
        (affineSpan ℝ (SimplicialRealization.projectivePolytope height)).direction =
          Fintype.card E ∧
      SimplicialRealization.HasSimplicialBoundary height ∧
      SimplicialRealization.boundaryHPolynomial height =
        (supportPolynomial (E := E)).map (Nat.castRingHom ℤ) :=
  SimplicialRealization.preorder_actual_simplicial_realization

end ResearchMain.PreorderGamma
