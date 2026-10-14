import AperyMoments.CorrectionCutScale
import AperyMoments.CorrectionCutWeight

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem correctionParameter_im_neg {b v : ℝ} {w : ℂ}
    (hw : w.im < 0) (hb : b < w.re) (hv : 0 < v) : (correctionParameter b w v).im < 0 := by
  rw [correctionParameter_im]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (sub_pos.mpr hb) hw) (sq_pos_of_pos hv)) (by norm_num)

theorem correctionCut_first_elliptic_bound {b : ℝ} {w : ℂ}
    (hw : 0 < (w.re - b) ^ 2 - w.im ^ 2) {v : ℝ} (hv : v ∈ Ioo 0 1) :
    ‖complexEllipticK (correctionParameter b w (v / correctionCutScale b w))‖ ≤
      (Real.pi / 2) * (1 - v) ^ (-(1 / 2 : ℝ)) := by
  have hre := correctionParameter_first_re hw v
  have hv2 : v ^ 2 < 1 := by nlinarith [hv.1, hv.2]
  have h := complexEllipticK_re_bound_below (by rw [hre]; exact hv2)
  rw [hre] at h
  apply h.trans
  apply (ellipticK_elementary_bound (sq_nonneg v) hv2).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_nonpos (by linarith [hv.2] : 0 < 1 - v)
    (by nlinarith [hv.1, hv.2] : 1 - v ≤ 1 - v ^ 2) (by norm_num)

theorem correctionCut_second_elliptic_bound {b δ : ℝ} (hδ : 0 < δ) {w : ℂ}
    (hw : w.im < 0) (hb : b < w.re) (hscale : δ ≤ correctionCutScale b w - 1)
    {v : ℝ} (hv : v ∈ Ioo 0 1) :
    ‖complexEllipticK (correctionParameter b w
      ((1 + (correctionCutScale b w - 1) * v) / correctionCutScale b w))‖ ≤
      ((Real.pi / 2) * (δ ^ (-(1 / 2 : ℝ)) + 1)) * v ^ (-(1 / 2 : ℝ)) := by
  have hA : 1 < correctionCutScale b w := by linarith
  have hA0 : 0 < correctionCutScale b w := by linarith
  have hraw : 0 < (w.re - b) ^ 2 - w.im ^ 2 := by
    have hs : 0 < Real.sqrt ((w.re - b) ^ 2 - w.im ^ 2) := by
      dsimp [correctionCutScale] at hA0
      linarith
    exact Real.sqrt_pos.mp hs
  have hcv : 0 < (correctionCutScale b w - 1) * v := mul_pos (by linarith) hv.1
  have hx : 0 < (1 + (correctionCutScale b w - 1) * v) / correctionCutScale b w := by positivity
  have hre := correctionParameter_second_re hraw v
  have hm : 1 < (1 + (correctionCutScale b w - 1) * v) ^ 2 := by nlinarith
  have h := complexEllipticK_re_bound_above (correctionParameter_im_neg hw hb hx)
    (by rw [hre]; exact hm)
  rw [hre] at h
  have hlower : δ * v ≤ (1 + (correctionCutScale b w - 1) * v) ^ 2 - 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hscale hv.1.le, sq_nonneg ((correctionCutScale b w - 1) * v)]
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos hδ hv.1) hlower
    (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
  rw [Real.mul_rpow hδ.le hv.1.le] at hp
  have hone : 1 ≤ v ^ (-(1 / 2 : ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos hv.1 hv.2.le (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
  apply h.trans
  nlinarith [Real.pi_pos]

end AperyMoments
