import MainTheorems.PreorderGamma.SimplicialRealization.ConeSaturation
import MainTheorems.PreorderGamma.HeightFaceSubsets

namespace ResearchMain.PreorderGamma.SimplicialRealization

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem quotientColumns_span :
    Submodule.span ℝ (Set.range fun v : QuotientIndex E => v.val) = ⊤ := by
  have hcolumn (v : QuotientIndex E) :
      integerVectorCast (integerQuotientVertex v) = v.val := integerQuotientVertex_cast v
  simpa only [hcolumn] using
    quotientIntegerColumns_span (E := E)

theorem boundaryVertexFaces_subset (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (hsimp : HasSimplicialBoundary height)
    (F S : Finset (QuotientIndex E)) (hF : F ∈ boundaryVertexFaces height) (hSF : S ⊆ F) :
    S ∈ boundaryVertexFaces height := by
  classical
  apply (mem_boundaryVertexFaces height S).mpr
  apply (boundaryVertexFace_iff_heightFace height hheight S).mpr
  by_cases hS : S = ∅
  · exact Or.inl hS
  · have hS' : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    have hface := (boundaryVertexFace_iff_heightFace height hheight F).mp
      ((mem_boundaryVertexFaces height F).mp hF)
    rcases hface with hFzero | ⟨l, hl, hb, ht, hn⟩
    · rw [hFzero] at hSF
      exact False.elim (hS (Finset.subset_empty.mp hSF))
    · have hlin : LinearIndepOn ℝ (fun v : QuotientIndex E => v.val)
          (F : Set (QuotientIndex E)) :=
        boundary_face_original_linearIndependent height hheight hsimp F hF
      obtain ⟨l', hl', hb', ht'⟩ := height_face_subset_nonzero_support
        (fun v : QuotientIndex E => v.val) height (F : Set (QuotientIndex E))
        (S : Set (QuotientIndex E)) hlin hSF hS' quotientColumns_span hheight l hb ht
      exact Or.inr ⟨l', hl', hb', ht', hS'⟩

end ResearchMain.PreorderGamma.SimplicialRealization
