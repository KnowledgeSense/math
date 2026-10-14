import MainTheorems.PreorderGamma.SimplicialRealization.Empty
import MainTheorems.PreorderGamma.SimplicialRealization.Singleton

namespace ResearchMain.PreorderGamma.SimplicialRealization

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem supportPolynomial_empty [IsEmpty E] :
    supportPolynomial (E := E) = 1 := by
  rw [preorder_gamma_expansion]
  simp

theorem low_dimension_actual_simplicial_realization (hn : Fintype.card E ≤ 1) :
    ∃ height : QuotientIndex E → ℝ,
      (∀ v, 0 < height v) ∧
      Module.finrank ℝ (affineSpan ℝ (projectivePolytope height)).direction =
        Fintype.card E ∧ HasSimplicialBoundary height ∧
      boundaryHPolynomial height =
        (supportPolynomial (E := E)).map (Nat.castRingHom ℤ) := by
  classical
  by_cases hz : Fintype.card E = 0
  · let : IsEmpty E := Fintype.card_eq_zero_iff.mp hz
    refine ⟨fun _ => 1, fun _ => zero_lt_one,
      projectivePolytope_dimension _ (fun _ => zero_lt_one),
      hasSimplicialBoundary_empty _, ?_⟩
    rw [boundaryHPolynomial_empty, supportPolynomial_empty]
    simp
  · have ho : Fintype.card E = 1 := by omega
    obtain ⟨inst⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp ho
    let : Unique E := inst
    obtain ⟨height, hh, hd, hs, hp⟩ := singleton_actual_simplicial_realization (E := E)
    exact ⟨height, hh, by simpa only [ho] using hd, hs, hp⟩

end ResearchMain.PreorderGamma.SimplicialRealization
