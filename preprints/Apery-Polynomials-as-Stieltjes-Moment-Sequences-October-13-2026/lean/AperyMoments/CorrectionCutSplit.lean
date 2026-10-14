import AperyMoments.CorrectionCutIntegralLimits

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem affine_intervalIntegrable_iff (F : ℝ → ℂ) (a : ℝ) {c : ℝ} (hc : 0 < c) :
    IntervalIntegrable F volume a (a + c) ↔
      IntervalIntegrable (fun v : ℝ => c • F (a + c * v)) volume 0 1 := by
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioo (0 : ℝ) 1) (f := fun v : ℝ => c * v + a) (f' := fun _ => c)
    measurableSet_Ioo (fun v _ => by simpa only [mul_one, id_eq] using
      (((hasDerivAt_id v).const_mul c).add_const a).hasDerivWithinAt)
    (fun _ _ _ _ he => mul_left_cancel₀ hc.ne' (add_right_cancel he)) F
  rw [image_affine_Ioo hc, mul_zero, zero_add, mul_one, add_comm c a] at hi
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith : a ≤ a + c),
    intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simpa only [abs_of_pos hc, add_comm] using hi

theorem affine_intervalIntegral (F : ℝ → ℂ) (a c : ℝ) :
    (∫ u in a..a + c, F u) = ∫ v in (0 : ℝ)..1, c • F (a + c * v) := by
  rw [intervalIntegral.integral_smul]
  simpa only [mul_zero, add_zero, mul_one] using
    (intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1) F c a).symm

theorem correctionSecondPoint_affine {b : ℝ} {w : ℂ}
    (hA : correctionCutScale b w ≠ 0) (v : ℝ) :
    correctionSecondPoint b w v =
      (correctionCutScale b w)⁻¹ + (1 - (correctionCutScale b w)⁻¹) * v := by
  unfold correctionSecondPoint
  field_simp

theorem correctionCut_integrable_of_halves {b : ℝ} {w : ℂ} (hA : 1 < correctionCutScale b w)
    (hfirst : IntervalIntegrable (correctionFirstKernel b w) volume 0 1)
    (hsecond : IntervalIntegrable (correctionSecondKernel b w) volume 0 1) :
    IntervalIntegrable (fun v => correctionRegular b w v * (correctionWeight v : ℂ)) volume 0 1 := by
  have hA0 : 0 < correctionCutScale b w := by linarith
  have hinv : (correctionCutScale b w)⁻¹ < 1 := (inv_lt_one₀ hA0).mpr hA
  let F : ℝ → ℂ := fun v => correctionRegular b w v * (correctionWeight v : ℂ)
  have hf : IntervalIntegrable F volume 0 (correctionCutScale b w)⁻¹ := by
    have h := (affine_intervalIntegrable_iff F 0 (inv_pos.mpr hA0)).mpr (by
      unfold correctionFirstKernel at hfirst
      simpa only [F, zero_add, div_eq_inv_mul] using hfirst)
    simpa only [zero_add] using h
  have hs : IntervalIntegrable F volume (correctionCutScale b w)⁻¹ 1 := by
    have h := (affine_intervalIntegrable_iff F (correctionCutScale b w)⁻¹
      (sub_pos.mpr hinv)).mpr (by
        unfold correctionSecondKernel at hsecond
        simp_rw [correctionSecondPoint_affine hA0.ne'] at hsecond
        exact hsecond)
    simpa only [add_sub_cancel] using h
  exact hf.trans hs

theorem correctionCut_integral_split {b : ℝ} {w : ℂ} (hA : 1 < correctionCutScale b w)
    (hi : IntervalIntegrable (fun v => correctionRegular b w v * (correctionWeight v : ℂ)) volume 0 1) :
    (∫ v in (0 : ℝ)..1, correctionRegular b w v * (correctionWeight v : ℂ)) =
      (∫ v in (0 : ℝ)..1, correctionFirstKernel b w v) +
      (∫ v in (0 : ℝ)..1, correctionSecondKernel b w v) := by
  have hA0 : 0 < correctionCutScale b w := by linarith
  have hinv : (correctionCutScale b w)⁻¹ < 1 := (inv_lt_one₀ hA0).mpr hA
  have hinv0 := (inv_pos.mpr hA0).le
  have hf := hi.mono_set (show uIcc 0 (correctionCutScale b w)⁻¹ ⊆ uIcc 0 1 by
    rw [uIcc_of_le hinv0, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hinv.le)
  have hs := hi.mono_set (show uIcc (correctionCutScale b w)⁻¹ 1 ⊆ uIcc 0 1 by
    rw [uIcc_of_le hinv.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hinv0 le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hf hs]
  have hfirst := affine_intervalIntegral (fun v => correctionRegular b w v * (correctionWeight v : ℂ))
    0 (correctionCutScale b w)⁻¹
  simp only [zero_add, ← div_eq_inv_mul] at hfirst
  have hsecond := affine_intervalIntegral (fun v => correctionRegular b w v * (correctionWeight v : ℂ))
    (correctionCutScale b w)⁻¹ (1 - (correctionCutScale b w)⁻¹)
  simp only [add_sub_cancel] at hsecond
  rw [hfirst, hsecond]
  congr 1
  apply intervalIntegral.integral_congr
  intro v _
  unfold correctionSecondKernel
  rw [correctionSecondPoint_affine hA0.ne']

end AperyMoments
