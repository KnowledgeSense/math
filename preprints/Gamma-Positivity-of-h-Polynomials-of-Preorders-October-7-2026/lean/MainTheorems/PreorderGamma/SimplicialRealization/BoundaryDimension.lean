import MainTheorems.PreorderGamma.SimplicialRealization.ProjectiveSupporting

namespace ResearchMain.PreorderGamma.SimplicialRealization

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem boundary_face_linearIndependent (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (hboundary : HasSimplicialBoundary height)
    (s : Finset (QuotientIndex E)) (hs : s ∈ boundaryVertexFaces height) :
    LinearIndependent ℝ (fun v : s => projectiveVertex height v.val) := by
  classical
  have ha := hboundary s hs
  have hf := (boundaryVertexFace_iff_heightFace height hheight s).mp
    ((mem_boundaryVertexFaces height s).mp hs)
  rcases hf with hzero | ⟨l, hl, hb, ht, hn⟩
  · subst s
    exact linearIndependent_empty_type
  · have htight : ∀ v : s, l (projectiveVertex height v.val) = 1 := by
      intro v
      exact (projectiveVertex_eq_iff height hheight l v.val).mpr ((ht v.val).mp v.property)
    apply linearIndependent_iff'.mpr
    intro t w hw i hi
    have hsum : ∑ v ∈ t, w v = 0 := by
      have h := congrArg l hw
      simp only [map_sum, map_smul, map_zero, smul_eq_mul, htight, mul_one] at h
      exact h
    exact ha.eq_zero_of_sum_eq_zero hsum hw i hi

theorem boundary_face_card_le_dimension (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (hboundary : HasSimplicialBoundary height)
    (s : Finset (QuotientIndex E)) (hs : s ∈ boundaryVertexFaces height) :
    s.card ≤ Fintype.card E := by
  have h := (boundary_face_linearIndependent height hheight hboundary s hs).fintype_card_le_finrank
  simpa using h

theorem boundary_face_original_linearIndependent (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (hboundary : HasSimplicialBoundary height)
    (s : Finset (QuotientIndex E)) (hs : s ∈ boundaryVertexFaces height) :
    LinearIndependent ℝ (fun v : s => v.val.val) := by
  have h := (boundary_face_linearIndependent height hheight hboundary s hs).units_smul
    (fun v : s => Units.mk0 (height v.val) (ne_of_gt (hheight v.val)))
  convert h using 1
  funext v
  change v.val.val = height v.val • ((height v.val)⁻¹ • v.val.val)
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (hheight v.val)), one_smul]

end ResearchMain.PreorderGamma.SimplicialRealization
