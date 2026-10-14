import AperyMoments.CorrectionRightValue

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def rightCorrectionComplex (b w : ℝ) : ℂ :=
  Real.pi⁻¹ • ∫ u in b..w,
    (Real.sqrt (u ^ 2 - b ^ 2))⁻¹ • complexEllipticK (((w - u) ^ 2 / 16 : ℝ) : ℂ)

theorem right_correction_jacobian {b w v : ℝ} (hb : 0 < b) (hw : b < w) (hv : v ∈ Icc 0 1) :
    (w - b) * (Real.sqrt ((w - (w - b) * v) ^ 2 - b ^ 2))⁻¹ =
      (w - b) * (w - b) ^ (-(1 / 2 : ℝ)) *
        ((b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) * correctionWeight v) := by
  have ha : 0 < w - b := sub_pos.mpr hw
  have hc : 0 < b * (1 + v) + w * (1 - v) := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hv.2)]
  have hd : 0 ≤ 1 - v := sub_nonneg.mpr hv.2
  have hs : (w - (w - b) * v) ^ 2 - b ^ 2 =
      ((w - b) * (1 - v)) * (b * (1 + v) + w * (1 - v)) := by ring
  rw [← inverse_sqrt_rpow (by rw [hs]; positivity), hs,
    Real.mul_rpow (mul_nonneg ha.le hd) hc.le, Real.mul_rpow ha.le hd]
  unfold correctionWeight
  ring

theorem rightCorrectionComplex_factored {b w : ℝ} (hb : 0 < b) (hw : b < w) :
    rightCorrectionComplex b w = ((w - b) * (w - b) ^ (-(1 / 2 : ℝ)) / Real.pi) •
      ∫ v in (0 : ℝ)..1,
        ((b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) * correctionWeight v) •
          complexEllipticK (((((w - b) * v / 4) ^ 2 : ℝ)) : ℂ) := by
  have he := intervalIntegral.smul_integral_comp_sub_mul (a := (0 : ℝ)) (b := 1)
    (fun u : ℝ => (Real.sqrt (u ^ 2 - b ^ 2))⁻¹ • complexEllipticK (((w - u) ^ 2 / 16 : ℝ) : ℂ)) (w - b) w
  simp only [mul_zero, sub_zero, mul_one, sub_sub_cancel] at he
  unfold rightCorrectionComplex
  rw [← he, ← intervalIntegral.integral_smul]
  have hi : (∫ v in (0 : ℝ)..1, (w - b) •
      ((Real.sqrt ((w - (w - b) * v) ^ 2 - b ^ 2))⁻¹ • complexEllipticK ((((w - b) * v) ^ 2 / 16 : ℝ) : ℂ))) =
      ((w - b) * (w - b) ^ (-(1 / 2 : ℝ))) •
        ∫ v in (0 : ℝ)..1,
          ((b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) * correctionWeight v) •
            complexEllipticK (((((w - b) * v / 4) ^ 2 : ℝ)) : ℂ) := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    dsimp only
    rw [smul_smul, right_correction_jacobian hb hw hv, smul_smul]
    rw [show ((((w - b) * v) ^ 2 / 16 : ℝ) : ℂ) = (((((w - b) * v / 4) ^ 2 : ℝ)) : ℂ) by congr 1; ring]
  rw [hi, smul_smul]
  congr 1
  ring

/-- The principal real correction equals i times the actual complex elliptic integral,
including the portion beyond its elliptic branch cut. -/
theorem continuedCorrection_right_complex_value {b w : ℝ} (hb : 0 < b) (hw : b < w) :
    continuedCorrection b (w : ℂ) = Complex.I * rightCorrectionComplex b w := by
  rw [rightCorrectionComplex_factored hb hw]
  unfold continuedCorrection
  rw [← Complex.ofReal_sub, inverse_sqrt_cpow_of_neg (by linarith : b - w < 0),
    show -(b - w) = w - b by ring]
  have he : (∫ v in (0 : ℝ)..1, correctionRegular b (w : ℂ) v * (correctionWeight v : ℂ)) =
      ∫ v in (0 : ℝ)..1,
        ((b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) * correctionWeight v) •
          complexEllipticK (((((w - b) * v / 4) ^ 2 : ℝ)) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    have hbase : correctionBase b (w : ℂ) v = ((b * (1 + v) + w * (1 - v) : ℝ) : ℂ) := by
      unfold correctionBase
      push_cast
      rfl
    have hpos : 0 < b * (1 + v) + w * (1 - v) := by
      nlinarith [mul_nonneg (sub_pos.mpr hw).le (sub_nonneg.mpr hv.2)]
    dsimp only
    unfold correctionRegular correctionParameter
    have hp : (((w : ℂ) - b) * (v : ℂ) / 4) ^ 2 = (((((w - b) * v / 4) ^ 2 : ℝ)) : ℂ) := by push_cast; rfl
    rw [hp, hbase, inverse_sqrt_cpow_of_nonneg hpos.le, Complex.real_smul]
    push_cast
    ring
  rw [he, Complex.real_smul]
  push_cast
  ring

end AperyMoments
