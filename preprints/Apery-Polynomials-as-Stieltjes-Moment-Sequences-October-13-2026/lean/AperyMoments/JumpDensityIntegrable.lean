import AperyMoments.JumpDensityBounds

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

/-- The actual nonnegative jump density is Lebesgue integrable, with its zero
singularity controlled rather than removed by a definition. -/
theorem reciprocalMomentDensity_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Integrable (reciprocalMomentDensity α) := by
  obtain ⟨ε,A,hε,hA,hnear⟩ := reciprocalMomentDensity_zero_bound hα
  let δ := min (ε/2) 1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ < ε := (min_le_left (ε/2) 1).trans_lt (by linarith)
  have hδ64 : δ ≤ 64 := (min_le_right (ε/2) 1).trans (by norm_num)
  obtain ⟨B,hB,hfar⟩ := reciprocalMomentDensity_bounded_away_zero hα hδ
  have he : ∀ᵐ x : ℝ ∂volume, x ∉ jumpExceptionalSet α := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using (jumpExceptionalSet_finite α).measure_zero volume
  have hipow : IntegrableOn (fun x : ℝ => x ^ (-(1/2 : ℝ))) (Ioo 0 δ) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hδ.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  have hiNear : IntegrableOn (reciprocalMomentDensity α) (Ioo 0 δ) := by
    apply (hipow.const_mul A).mono' (reciprocalMomentDensity_measurable α).aestronglyMeasurable
    filter_upwards [ae_restrict_of_ae he, self_mem_ae_restrict measurableSet_Ioo] with x hex hx
    rw [Real.norm_eq_abs, abs_of_nonneg (reciprocalMomentDensity_nonneg hα.le x)]
    have hh := hnear x hx.1 (hx.2.trans hδε) hex
    simpa only [div_eq_mul_inv, ← inverse_sqrt_rpow hx.1.le] using hh
  have hiFar : IntegrableOn (reciprocalMomentDensity α) (Icc δ 64) := by
    have hic : IntegrableOn (fun _ : ℝ => B) (Icc δ 64) := continuous_const.integrableOn_Icc
    apply hic.mono' (reciprocalMomentDensity_measurable α).aestronglyMeasurable
    filter_upwards [ae_restrict_of_ae he, self_mem_ae_restrict measurableSet_Icc] with x hex hx
    rw [Real.norm_eq_abs, abs_of_nonneg (reciprocalMomentDensity_nonneg hα.le x)]
    exact hfar x hx hex
  have hset : Ioo (0 : ℝ) δ ∪ Icc δ 64 = Ioc 0 64 := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact ⟨hx.1, hx.2.le.trans hδ64⟩
      · exact ⟨hδ.trans_le hx.1, hx.2⟩
    · intro hx
      by_cases hh : x < δ
      · exact Or.inl ⟨hx.1,hh⟩
      · exact Or.inr ⟨le_of_not_gt hh,hx.2⟩
  have hi : IntegrableOn (reciprocalMomentDensity α) (Ioc 0 64) := by
    rw [← hset]
    exact hiNear.union hiFar
  have hz : ∀ x : ℝ, x ∉ Ioc 0 64 → reciprocalMomentDensity α x = 0 := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp [reciprocalMomentDensity]
    · apply reciprocalMomentDensity_support hα hα1
      intro hmem
      exact hx ⟨lt_of_le_of_ne hmem.1 (Ne.symm hx0),hmem.2⟩
  have hid : reciprocalMomentDensity α = (Ioc 0 64).indicator (reciprocalMomentDensity α) := by
    funext x
    by_cases hx : x ∈ Ioc 0 64
    · simp [hx]
    · simp [hx,hz x hx]
  rw [hid]
  exact hi.integrable_indicator measurableSet_Ioc

end AperyMoments
