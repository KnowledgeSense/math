import AperyMoments.CandidateDensity
import AperyMoments.CorrectionRightContinuity
import AperyMoments.CorrectionRealIntegral

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def rightCorrectionReal (b w : ℝ) : ℝ :=
  (w - b) * (w - b) ^ (-(1 / 2 : ℝ)) / Real.pi *
    ∫ v in (0 : ℝ)..1, ellipticK (((w - b) * v / 4) ^ 2) *
      (b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) * correctionWeight v

theorem correctionRegular_ofReal_before_cut {b w v : ℝ} (hb : 0 < b)
    (hw : b < w) (hw4 : w < b + 4) (hv : v ∈ Icc 0 1) :
    correctionRegular b (w : ℂ) v =
      ((ellipticK (((w - b) * v / 4) ^ 2) *
        (b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hp : correctionParameter b (w : ℂ) v = ((((w - b) * v / 4) ^ 2 : ℝ) : ℂ) := by
    unfold correctionParameter
    push_cast
    rfl
  have hB : correctionBase b (w : ℂ) v = ((b * (1 + v) + w * (1 - v) : ℝ) : ℂ) := by
    unfold correctionBase
    push_cast
    rfl
  have hn : ‖(w : ℂ) - b‖ < 4 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hw)]
    linarith
  have hm := correctionParameter_mem_domain_central hn hv
  rw [hp] at hm
  have hm1 : ((w - b) * v / 4) ^ 2 < 1 := hm.resolve_left (by simp only [Complex.ofReal_im, ne_eq, not_not])
  have hbase := Complex.mem_slitPlane_iff.mp (correctionBase_mem_slitPlane_central (w := (w : ℂ)) hb
    (by simpa using (show -b < w by linarith)) hv)
  rw [hB] at hbase
  have hb0 : 0 < b * (1 + v) + w * (1 - v) := hbase.resolve_right (by simp)
  unfold correctionRegular
  rw [hp, hB, complexEllipticK_ofReal hm1, inverse_sqrt_cpow_of_nonneg hb0.le, Complex.ofReal_mul]

theorem continuedCorrection_right_value_before_cut {b w : ℝ} (hb : 0 < b)
    (hw : b < w) (hw4 : w < b + 4) :
    continuedCorrection b (w : ℂ) = Complex.I * (rightCorrectionReal b w : ℂ) := by
  unfold continuedCorrection rightCorrectionReal
  rw [← Complex.ofReal_sub, inverse_sqrt_cpow_of_neg (by linarith : b - w < 0)]
  have he : (∫ v in (0 : ℝ)..1, correctionRegular b (w : ℂ) v * (correctionWeight v : ℂ)) =
      ((∫ v in (0 : ℝ)..1, ellipticK (((w - b) * v / 4) ^ 2) *
        (b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) * correctionWeight v : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    dsimp only
    rw [correctionRegular_ofReal_before_cut hb hw hw4 hv]
    push_cast
    rfl
  rw [he, show -(b - w) = w - b by ring]
  push_cast
  ring

theorem rightCorrectionReal_eq_integral {b w : ℝ} (hb : 0 < b) (hw : b < w) :
    rightCorrectionReal b w = Real.pi⁻¹ * ∫ u in b..w,
      ellipticK ((w - u) ^ 2 / 16) / Real.sqrt (u ^ 2 - b ^ 2) := by
  have he := intervalIntegral.smul_integral_comp_sub_mul (a := (0 : ℝ)) (b := 1)
    (fun u : ℝ => ellipticK ((w - u) ^ 2 / 16) / Real.sqrt (u ^ 2 - b ^ 2)) (w - b) w
  simp only [smul_eq_mul, mul_zero, sub_zero, mul_one, sub_sub_cancel] at he
  rw [← he, ← intervalIntegral.integral_const_mul]
  have hi : (∫ v in (0 : ℝ)..1, (w - b) *
      (ellipticK ((w - (w - (w - b) * v)) ^ 2 / 16) /
        Real.sqrt ((w - (w - b) * v) ^ 2 - b ^ 2))) =
      (w - b) * (w - b) ^ (-(1 / 2 : ℝ)) *
        ∫ v in (0 : ℝ)..1, ellipticK (((w - b) * v / 4) ^ 2) *
          (b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) * correctionWeight v := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    have ha : 0 < w - b := sub_pos.mpr hw
    have hc : 0 < b * (1 + v) + w * (1 - v) := by
      have hv0 := hv.1
      have hv1 := hv.2
      nlinarith [mul_nonneg (by linarith : 0 ≤ w - b) (by linarith : 0 ≤ 1 - v)]
    have hd : 0 ≤ 1 - v := by linarith [hv.2]
    have hs : (w - (w - b) * v) ^ 2 - b ^ 2 =
        ((w - b) * (1 - v)) * (b * (1 + v) + w * (1 - v)) := by ring
    have hp : (w - (w - (w - b) * v)) ^ 2 / 16 = (((w - b) * v / 4) ^ 2) := by ring
    dsimp only
    rw [hp, div_eq_mul_inv, ← inverse_sqrt_rpow (by rw [hs]; positivity), hs,
      Real.mul_rpow (mul_nonneg ha.le hd) hc.le, Real.mul_rpow ha.le hd]
    unfold correctionWeight
    ring
  simp only [sub_sub_cancel] at hi
  rw [hi]
  unfold rightCorrectionReal
  ring

theorem continuationCorrection_before_cut {b w : ℝ} (hb : 0 < b) (hw : b < w)
    (hw4 : w < b + 4) :
    continuationCorrection b w = rightCorrectionReal b w / Real.pi ^ 2 := by
  rw [rightCorrectionReal_eq_integral hb hw]
  unfold continuationCorrection
  have he : (∫ u in b..w, ellipticKappa ((w - u) ^ 2 / 16) / Real.sqrt (u ^ 2 - b ^ 2)) =
      ∫ u in b..w, ellipticK ((w - u) ^ 2 / 16) / Real.sqrt (u ^ 2 - b ^ 2) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hw.le] at hu
    have hm : (w - u) ^ 2 / 16 ≤ 1 := by nlinarith [hu.1, hu.2]
    dsimp only
    rw [ellipticKappa, ite_eq_left hm]
  rw [he]
  ring

end AperyMoments
