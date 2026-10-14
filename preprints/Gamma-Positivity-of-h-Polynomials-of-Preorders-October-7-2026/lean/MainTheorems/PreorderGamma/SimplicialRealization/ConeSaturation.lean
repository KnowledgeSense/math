import MainTheorems.PreorderGamma.SimplicialRealization.IntegralCones
import MainTheorems.PreorderGamma.IntegerConeCoordinates

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem quotientIntegerColumns_span :
    Submodule.span ℝ (Set.range fun v : QuotientIndex E =>
      integerVectorCast (integerQuotientVertex v)) = ⊤ := by
  apply top_unique
  intro x hx
  rw [← Finset.univ_sum_single x]
  apply Submodule.sum_mem
  intro i hi
  have hu : Pi.single i (1 : ℝ) ∈ Submodule.span ℝ
      (Set.range fun v : QuotientIndex E => integerVectorCast (integerQuotientVertex v)) := by
    apply Submodule.subset_span
    exact ⟨unitIndex i, integerQuotientVertex_cast _⟩
  have heq : Pi.single i (x i) = x i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [heq]
  exact Submodule.smul_mem _ (x i) hu

theorem boundary_positive_coordinates_integral (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (hsimp : HasSimplicialBoundary height)
    (s : Finset (QuotientIndex E)) (hs : s ∈ boundaryVertexFaces height)
    (z : E → ℤ) (c : s → ℝ) (hc : ∀ v, 0 < c v)
    (hz : (∑ v : s, c v • v.val.val) = fun i => (z i : ℝ)) :
    ∃ a : s → ℕ, (∀ v, 0 < a v ∧ c v = (a v : ℝ)) ∧
      integralCombination s a = z := by
  let e : s ≃ (s : Set (QuotientIndex E)) := s.equivToSet
  have hmat : (integerConfigurationMatrix (integerQuotientVertex (E := E))).IsTotallyUnimodular :=
    quotientIntegerMatrix_totallyUnimodular
  have hcolumn (v : QuotientIndex E) :
      integerVectorCast (integerQuotientVertex v) = v.val := integerQuotientVertex_cast v
  have hlin : LinearIndepOn ℝ
      (fun v : QuotientIndex E => integerVectorCast (integerQuotientVertex v))
      (s : Set (QuotientIndex E)) := by
    change LinearIndependent ℝ (fun v : (s : Set (QuotientIndex E)) =>
      integerVectorCast (integerQuotientVertex v.val))
    have h := (boundary_face_original_linearIndependent height hheight hsimp s hs).comp
      e.symm e.symm.injective
    convert h using 1
    funext v
    exact hcolumn v.val
  obtain ⟨a, ha, haz⟩ := integer_independent_combination_positive
    (integerQuotientVertex (E := E)) (s : Set (QuotientIndex E)) hmat hlin
    quotientIntegerColumns_span z (fun v => c (e.symm v)) (by
      have hsum : integerVectorCast z =
          ∑ v : s, c v • integerVectorCast (integerQuotientVertex v.val) := by
        change (fun i : E => (z i : ℝ)) = _
        simpa only [hcolumn] using hz.symm
      have heq := Fintype.sum_equiv e
        (fun v : s => c v • integerVectorCast (integerQuotientVertex v.val))
        (fun v : (s : Set (QuotientIndex E)) =>
          c (e.symm v) • integerVectorCast (integerQuotientVertex v.val))
        (fun v => by rw [e.symm_apply_apply]; rfl)
      refine hsum.trans (heq.trans ?_)
      apply Finset.sum_congr
      · ext v
        simp only [Finset.mem_univ]
      · intro v hv
        rfl)
    (fun v => hc (e.symm v))
  refine ⟨fun v => a (e v), ?_, ?_⟩
  · intro v
    simpa only [e.symm_apply_apply] using ha (e v)
  · change (∑ v : s, (a (e v) : ℤ) • integerQuotientVertex v.val) = z
    rw [← haz]
    have heq := Fintype.sum_equiv e
      (fun v : s => (a (e v) : ℤ) • integerQuotientVertex v.val)
      (fun v : (s : Set (QuotientIndex E)) => (a v : ℤ) • integerQuotientVertex v.val)
      (fun v => rfl)
    refine heq.trans ?_
    apply Finset.sum_congr
    · ext v
      simp only [Finset.mem_univ]
    · intro v hv
      rfl

end ResearchMain.PreorderGamma.SimplicialRealization
