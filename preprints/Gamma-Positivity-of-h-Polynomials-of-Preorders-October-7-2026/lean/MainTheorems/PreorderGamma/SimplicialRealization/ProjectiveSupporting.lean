import MainTheorems.PreorderGamma.SimplicialRealization.ProjectivePolytope

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem projectiveVertex_le_iff (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (l : (E → ℝ) →ₗ[ℝ] ℝ)
    (v : QuotientIndex E) :
    l (projectiveVertex height v) ≤ 1 ↔ l v.val ≤ height v := by
  simp only [projectiveVertex, map_smul, smul_eq_mul]
  exact inv_mul_le_one₀ (hheight v)

theorem projectiveVertex_eq_iff (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (l : (E → ℝ) →ₗ[ℝ] ℝ)
    (v : QuotientIndex E) :
    l (projectiveVertex height v) = 1 ↔ l v.val = height v := by
  simp only [projectiveVertex, map_smul, smul_eq_mul]
  simpa only [mul_one] using
    inv_mul_eq_iff_eq_mul₀ (a := height v) (b := l v.val) (c := (1 : ℝ))
      (ne_of_gt (hheight v))

theorem projective_support_value_pos (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (l : (E → ℝ) →ₗ[ℝ] ℝ) (hl : l ≠ 0)
    (m : ℝ) (hbound : ∀ v, l (projectiveVertex height v) ≤ m) : 0 < m := by
  by_contra hm
  have hm : m ≤ 0 := le_of_not_gt hm
  have hz : ∀ a : E, l (Pi.single a (1 : ℝ)) = 0 := by
    intro a
    have hp : l (Pi.single a (1 : ℝ)) ≤ height (unitIndex a) * m := by
      have h := hbound (unitIndex a)
      simp only [projectiveVertex, unitIndex, map_smul, smul_eq_mul] at h
      exact (inv_mul_le_iff₀ (hheight (unitIndex a))).mp h
    have hn : -l (Pi.single a (1 : ℝ)) ≤ height (negUnitIndex a) * m := by
      have h := hbound (negUnitIndex a)
      simp only [projectiveVertex, negUnitIndex, map_smul, map_neg, smul_eq_mul] at h
      exact (inv_mul_le_iff₀ (hheight (negUnitIndex a))).mp h
    have hp0 : height (unitIndex a) * m ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hheight _)) hm
    have hn0 : height (negUnitIndex a) * m ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hheight _)) hm
    linarith
  apply hl
  apply LinearMap.ext
  intro x
  change l x = 0
  rw [← Finset.univ_sum_single x, map_sum]
  change (∑ a : E, l (Pi.single a (x a))) = 0
  apply Finset.sum_eq_zero
  intro a ha
  have heq : Pi.single a (x a) = x a • Pi.single a (1 : ℝ) := by
    ext b
    simp [Pi.single_apply]
  rw [heq, map_smul, hz a, smul_zero]

def IsHeightFace (height : QuotientIndex E → ℝ)
    (s : Finset (QuotientIndex E)) : Prop :=
  s = ∅ ∨ ∃ l : (E → ℝ) →ₗ[ℝ] ℝ, l ≠ 0 ∧
    (∀ v, l v.val ≤ height v) ∧
    (∀ v, v ∈ s ↔ l v.val = height v) ∧ s.Nonempty

theorem boundaryVertexFace_iff_heightFace (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (s : Finset (QuotientIndex E)) :
    IsBoundaryVertexFace height s ↔ IsHeightFace height s := by
  constructor
  · rintro (hs | ⟨l, hl, m, hbound, htight, hs⟩)
    · exact Or.inl hs
    have hm := projective_support_value_pos height hheight l hl m hbound
    let l' : (E → ℝ) →ₗ[ℝ] ℝ := m⁻¹ • l
    have hl' : l' ≠ 0 := by
      intro h
      apply hl
      have h' := congrArg (fun f : (E → ℝ) →ₗ[ℝ] ℝ => m • f) h
      simpa [l', smul_smul, ne_of_gt hm] using h'
    refine Or.inr ⟨l', hl', ?_, ?_, hs⟩
    · intro v
      apply (projectiveVertex_le_iff height hheight l' v).mp
      change m⁻¹ * l (projectiveVertex height v) ≤ 1
      exact (inv_mul_le_one₀ hm).mpr (hbound v)
    · intro v
      rw [← projectiveVertex_eq_iff height hheight l' v]
      change v ∈ s ↔ m⁻¹ * l (projectiveVertex height v) = 1
      rw [inv_mul_eq_iff_eq_mul₀ (ne_of_gt hm), mul_one]
      exact htight v
  · rintro (hs | ⟨l, hl, hbound, htight, hs⟩)
    · exact Or.inl hs
    refine Or.inr ⟨l, hl, 1, ?_, ?_, hs⟩
    · intro v
      exact (projectiveVertex_le_iff height hheight l v).mpr (hbound v)
    · intro v
      rw [projectiveVertex_eq_iff height hheight l v]
      exact htight v

theorem zeroIndex_not_mem_boundaryFace (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (s : Finset (QuotientIndex E))
    (hs : s ∈ boundaryVertexFaces height) : zeroIndex ∉ s := by
  classical
  rcases (mem_boundaryVertexFaces height s).mp hs with hs | ⟨l, hl, m, hb, ht, hn⟩
  · simp [hs]
  · intro hz
    have hm := projective_support_value_pos height hheight l hl m hb
    have heq := (ht zeroIndex).mp hz
    simp only [projectiveVertex_zero, map_zero] at heq
    linarith

end ResearchMain.PreorderGamma.SimplicialRealization
