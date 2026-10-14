import MainTheorems.PreorderGamma.SimplicialRealization.ProjectiveSupporting
import MainTheorems.PreorderGamma.GammaExpansion

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E] [Unique E]

theorem quotientIndex_singleton_cases (v : QuotientIndex E) :
    v = zeroIndex ∨ v = unitIndex default ∨ v = negUnitIndex default := by
  rcases (mem_quotientVertices _).mp v.property with
    h | ⟨a, h⟩ | ⟨a, h⟩ | ⟨a, b, hab, h⟩
  · exact Or.inl (Subtype.ext h)
  · have ha : a = (default : E) := Subsingleton.elim _ _
    exact Or.inr (Or.inl (Subtype.ext (by simpa [unitIndex, ha] using h)))
  · have ha : a = (default : E) := Subsingleton.elim _ _
    exact Or.inr (Or.inr (Subtype.ext (by simpa [negUnitIndex, ha] using h)))
  · have ha : a = (default : E) := Subsingleton.elim _ _
    have hb : b = (default : E) := Subsingleton.elim _ _
    exact Or.inl (Subtype.ext (by simpa [zeroIndex, ha, hb] using h))

theorem singleton_zero_ne_unit : (zeroIndex : QuotientIndex E) ≠ unitIndex default := by
  intro h
  have h' := congrArg (fun v : QuotientIndex E => v.val default) h
  norm_num [zeroIndex, unitIndex] at h'

theorem singleton_zero_ne_negUnit :
    (zeroIndex : QuotientIndex E) ≠ negUnitIndex default := by
  intro h
  have h' := congrArg (fun v : QuotientIndex E => v.val default) h
  norm_num [zeroIndex, negUnitIndex] at h'

theorem singleton_unit_ne_negUnit :
    (unitIndex (default : E)) ≠ negUnitIndex default := by
  intro h
  have h' := congrArg (fun v : QuotientIndex E => v.val default) h
  norm_num [unitIndex, negUnitIndex] at h'

theorem singleton_unit_heightFace :
    IsHeightFace (fun _ : QuotientIndex E => 1) {unitIndex default} := by
  classical
  let l : (E → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj default
  have hl : l ≠ 0 := by
    intro h
    have h' := congrArg (fun f : (E → ℝ) →ₗ[ℝ] ℝ => f (Pi.single default 1)) h
    norm_num [l] at h'
  refine Or.inr ⟨l, hl, ?_, ?_, Finset.singleton_nonempty _⟩
  · intro v
    rcases quotientIndex_singleton_cases v with rfl | rfl | rfl <;>
      norm_num [l, zeroIndex, unitIndex, negUnitIndex]
  · intro v
    rcases quotientIndex_singleton_cases v with rfl | rfl | rfl <;>
      simp only [Finset.mem_singleton, singleton_zero_ne_unit,
        singleton_unit_ne_negUnit.symm] <;>
      norm_num [l, zeroIndex, unitIndex, negUnitIndex]

theorem singleton_negUnit_heightFace :
    IsHeightFace (fun _ : QuotientIndex E => 1) {negUnitIndex default} := by
  classical
  let l : (E → ℝ) →ₗ[ℝ] ℝ := -(LinearMap.proj default)
  have hl : l ≠ 0 := by
    intro h
    have h' := congrArg (fun f : (E → ℝ) →ₗ[ℝ] ℝ => f (Pi.single default 1)) h
    norm_num [l] at h'
  refine Or.inr ⟨l, hl, ?_, ?_, Finset.singleton_nonempty _⟩
  · intro v
    rcases quotientIndex_singleton_cases v with rfl | rfl | rfl <;>
      norm_num [l, zeroIndex, unitIndex, negUnitIndex]
  · intro v
    rcases quotientIndex_singleton_cases v with rfl | rfl | rfl <;>
      simp only [Finset.mem_singleton, singleton_zero_ne_negUnit,
        singleton_unit_ne_negUnit] <;>
      norm_num [l, zeroIndex, unitIndex, negUnitIndex]

theorem singleton_heightFace_cases (s : Finset (QuotientIndex E))
    (hs : IsHeightFace (fun _ : QuotientIndex E => 1) s) :
    s = ∅ ∨ s = {unitIndex default} ∨ s = {negUnitIndex default} := by
  classical
  rcases hs with hs | ⟨l, hl, hb, ht, hn⟩
  · exact Or.inl hs
  have hz : l (zeroIndex : QuotientIndex E).val = 0 := by simp [zeroIndex]
  have hneg : l (negUnitIndex (default : E)).val = -l (unitIndex default).val := by
    simp [negUnitIndex, unitIndex]
  obtain ⟨v, hv⟩ := hn
  rcases quotientIndex_singleton_cases v with rfl | rfl | rfl
  · have h := (ht zeroIndex).mp hv
    rw [hz] at h
    norm_num at h
  · have hu := (ht (unitIndex default)).mp hv
    refine Or.inr (Or.inl ?_)
    ext w
    rw [ht w]
    rcases quotientIndex_singleton_cases w with rfl | rfl | rfl
    · simp [hz, singleton_zero_ne_unit]
    · simp [hu]
    · norm_num [hneg, hu, singleton_unit_ne_negUnit.symm]
  · have hn := (ht (negUnitIndex default)).mp hv
    have hu : l (unitIndex (default : E)).val = -1 := by rw [hneg] at hn; linarith
    refine Or.inr (Or.inr ?_)
    ext w
    rw [ht w]
    rcases quotientIndex_singleton_cases w with rfl | rfl | rfl
    · simp [hz, singleton_zero_ne_negUnit]
    · norm_num [hu, singleton_unit_ne_negUnit]
    · simp [hn]

theorem boundaryVertexFaces_singleton :
    boundaryVertexFaces (fun _ : QuotientIndex E => 1) =
      {(∅ : Finset (QuotientIndex E)),
        ({unitIndex (default : E)} : Finset (QuotientIndex E)),
        ({negUnitIndex (default : E)} : Finset (QuotientIndex E))} := by
  classical
  ext s
  rw [mem_boundaryVertexFaces, boundaryVertexFace_iff_heightFace _ (fun _ => zero_lt_one)]
  constructor
  · intro hs
    rcases singleton_heightFace_cases s hs with rfl | rfl | rfl <;> simp
  · intro hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact singleton_unit_heightFace
    · exact singleton_negUnit_heightFace

theorem hasSimplicialBoundary_singleton :
    HasSimplicialBoundary (fun _ : QuotientIndex E => 1) := by
  classical
  intro s hs
  rw [boundaryVertexFaces_singleton] at hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl <;> exact affineIndependent_of_subsingleton ℝ _

theorem boundaryHPolynomial_singleton :
    boundaryHPolynomial (fun _ : QuotientIndex E => 1) = 1 + Polynomial.X := by
  classical
  simp [boundaryHPolynomial, boundaryVertexFaces_singleton, Fintype.card_unique,
    singleton_unit_ne_negUnit]

theorem supportPolynomial_singleton : (supportPolynomial (E := E)) = 1 + Polynomial.X := by
  rw [preorder_gamma_expansion]
  simp [Fintype.card_unique]

theorem singleton_actual_simplicial_realization :
    ∃ height : QuotientIndex E → ℝ,
      (∀ v, 0 < height v) ∧
      Module.finrank ℝ (affineSpan ℝ (projectivePolytope height)).direction = 1 ∧
      HasSimplicialBoundary height ∧
      boundaryHPolynomial height =
        (supportPolynomial (E := E)).map (Nat.castRingHom ℤ) := by
  refine ⟨fun _ => 1, fun _ => zero_lt_one, ?_,
    hasSimplicialBoundary_singleton, ?_⟩
  · rw [projectivePolytope_dimension _ (fun _ => zero_lt_one), Fintype.card_unique]
  · rw [boundaryHPolynomial_singleton, supportPolynomial_singleton]
    simp

end ResearchMain.PreorderGamma.SimplicialRealization
