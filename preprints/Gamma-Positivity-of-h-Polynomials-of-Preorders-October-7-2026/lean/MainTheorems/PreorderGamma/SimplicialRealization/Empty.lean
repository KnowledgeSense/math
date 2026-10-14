import MainTheorems.PreorderGamma.SimplicialRealization.ProjectivePolytope

namespace ResearchMain.PreorderGamma.SimplicialRealization

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E] [IsEmpty E]

theorem boundaryVertexFaces_empty (height : QuotientIndex E → ℝ) :
    boundaryVertexFaces height = {∅} := by
  classical
  ext s
  rw [mem_boundaryVertexFaces, Finset.mem_singleton]
  constructor
  · intro hs
    rcases hs with h | ⟨l, hl, m, hbound, hface, hn⟩
    · exact h
    · apply False.elim
      apply hl
      apply LinearMap.ext
      intro x
      change l x = 0
      have hx : x = (0 : E → ℝ) := Subsingleton.elim _ _
      simp [hx]
  · intro hs
    exact Or.inl hs

theorem hasSimplicialBoundary_empty (height : QuotientIndex E → ℝ) :
    HasSimplicialBoundary height := by
  classical
  intro s hs
  rw [boundaryVertexFaces_empty, Finset.mem_singleton] at hs
  subst s
  exact affineIndependent_of_subsingleton ℝ _

theorem boundaryHPolynomial_empty (height : QuotientIndex E → ℝ) :
    boundaryHPolynomial height = 1 := by
  classical
  simp [boundaryHPolynomial, boundaryVertexFaces_empty]

theorem empty_actual_simplicial_realization :
    ∃ height : QuotientIndex E → ℝ,
      (∀ v, 0 < height v) ∧ projectivePolytope height = {0} ∧
      HasSimplicialBoundary height ∧ boundaryHPolynomial height = 1 := by
  refine ⟨fun _ => 1, fun _ => zero_lt_one, projectivePolytope_empty _,
    hasSimplicialBoundary_empty _, boundaryHPolynomial_empty _⟩

end ResearchMain.PreorderGamma.SimplicialRealization
