import AperyMoments.CorrectionComplexValue
import AperyMoments.CorrectionOuterBoundary

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem complexEllipticK_ofReal_le {m : ℝ} (hm : m ≤ 1) :
    complexEllipticK m = (ellipticK m : ℂ) := by
  unfold complexEllipticK ellipticK
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro θ _
  have hp : 0 ≤ 1 - m * Real.sin θ ^ 2 := by
    nlinarith [sq_nonneg (Real.cos θ), Real.sin_sq_add_cos_sq θ,
      mul_nonneg (sub_nonneg.mpr hm) (sq_nonneg (Real.sin θ))]
  dsimp only
  rw [Complex.ofReal_cpow hp]
  push_cast
  norm_num

theorem complexEllipticK_re_eq_kappa (m : ℝ) :
    (complexEllipticK m).re = ellipticKappa m := by
  unfold ellipticKappa
  split_ifs with h
  · rw [complexEllipticK_ofReal_le h, Complex.ofReal_re]
  · exact complexEllipticK_cut_real_connection (lt_of_not_ge h)

theorem correctionRegular_real_weight {b w v : ℝ} (hb : 0 < b) (hw : b < w)
    (hv : v ∈ Icc 0 1) :
    correctionRegular b (w : ℂ) v * (correctionWeight v : ℂ) =
      ((b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) * correctionWeight v) •
        complexEllipticK (((((w - b) * v / 4) ^ 2 : ℝ)) : ℂ) := by
  have hbase : correctionBase b (w : ℂ) v = ((b * (1 + v) + w * (1 - v) : ℝ) : ℂ) := by
    unfold correctionBase
    push_cast
    rfl
  have hpos : 0 < b * (1 + v) + w * (1 - v) := by
    nlinarith [mul_nonneg (sub_pos.mpr hw).le (sub_nonneg.mpr hv.2)]
  unfold correctionRegular correctionParameter
  have hp : (((w : ℂ) - b) * (v : ℂ) / 4) ^ 2 = (((((w - b) * v / 4) ^ 2 : ℝ)) : ℂ) := by push_cast; rfl
  rw [hp, hbase, inverse_sqrt_cpow_of_nonneg hpos.le, Complex.real_smul]
  push_cast
  ring

theorem correctionRegular_real_integrable {b w : ℝ} (hb : 0 < b) (hw : b < w)
    (hne : w ≠ b + 4) :
    IntervalIntegrable (fun v => correctionRegular b (w : ℂ) v * (correctionWeight v : ℂ)) volume 0 1 := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hdisk : (w : ℂ) ∈ correctionRegularDisk b := by
      constructor
      · simp only [Complex.ofReal_re]; linarith
      · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hw)]
        linarith
    have hcont : ContinuousOn (correctionRegular b (w : ℂ)) (Icc 0 1) :=
      (correctionRegular_continuousOn_disk hb).comp (f := fun v : ℝ => ((w : ℂ), v))
        (by fun_prop) (fun _ hv => ⟨hdisk, hv⟩)
    have hi : IntervalIntegrable (fun v => (correctionWeight v : ℂ)) volume 0 1 :=
      ⟨correctionWeight_integrable.1.ofReal, correctionWeight_integrable.2.ofReal⟩
    exact IntervalIntegrable.continuousOn_mul hi
      (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcont)
  · exact correctionRegular_weight_integrable_after_cut hb h

theorem rightCorrectionComplex_re {b w : ℝ} (hb : 0 < b) (hw : b < w)
    (hne : w ≠ b + 4) :
    (rightCorrectionComplex b w).re = Real.pi ^ 2 * continuationCorrection b w := by
  let J : ℝ → ℂ := fun v =>
    ((b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) * correctionWeight v) •
      complexEllipticK (((((w - b) * v / 4) ^ 2 : ℝ)) : ℂ)
  have hi : IntervalIntegrable J volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (correctionRegular_real_integrable hb hw hne)
    apply (integrableOn_congr_fun _ measurableSet_Ioo).mp h
    intro v hv
    exact correctionRegular_real_weight hb hw ⟨hv.1.le, hv.2.le⟩
  have hre : (∫ v in (0 : ℝ)..1, J v).re = ∫ v in (0 : ℝ)..1,
      ((b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) * correctionWeight v) *
        ellipticKappa (((w - b) * v / 4) ^ 2) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    change RCLike.re (∫ v in Ioc (0 : ℝ) 1, J v) = _
    rw [← integral_re hi.1]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro v _
    change (J v).re = _
    simp only [J, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, complexEllipticK_re_eq_kappa]
  rw [rightCorrectionComplex_factored hb hw]
  change (((w - b) * (w - b) ^ (-(1 / 2 : ℝ)) / Real.pi) • ∫ v in (0 : ℝ)..1, J v).re = _
  rw [Complex.smul_re, hre]
  have he := intervalIntegral.smul_integral_comp_sub_mul (a := (0 : ℝ)) (b := 1)
    (fun u : ℝ => ellipticKappa ((w - u) ^ 2 / 16) / Real.sqrt (u ^ 2 - b ^ 2)) (w - b) w
  simp only [mul_zero, sub_zero, mul_one, sub_sub_cancel, smul_eq_mul] at he
  unfold continuationCorrection
  rw [← he, ← intervalIntegral.integral_const_mul]
  have hj : (∫ v in (0 : ℝ)..1, (w - b) *
      (ellipticKappa (((w - b) * v) ^ 2 / 16) / Real.sqrt ((w - (w - b) * v) ^ 2 - b ^ 2))) =
      ((w - b) * (w - b) ^ (-(1 / 2 : ℝ))) * ∫ v in (0 : ℝ)..1,
        ((b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) * correctionWeight v) *
          ellipticKappa (((w - b) * v / 4) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    dsimp only
    rw [div_eq_mul_inv, show (w - b) * (ellipticKappa (((w - b) * v) ^ 2 / 16) *
        (Real.sqrt ((w - (w - b) * v) ^ 2 - b ^ 2))⁻¹) =
        ((w - b) * (Real.sqrt ((w - (w - b) * v) ^ 2 - b ^ 2))⁻¹) *
          ellipticKappa (((w - b) * v) ^ 2 / 16) by ring,
      right_correction_jacobian hb hw hv]
    rw [show (((w - b) * v) ^ 2 / 16) = (((w - b) * v / 4) ^ 2) by ring]
    ring
  rw [hj]
  simp only [smul_eq_mul]
  field_simp

end AperyMoments
