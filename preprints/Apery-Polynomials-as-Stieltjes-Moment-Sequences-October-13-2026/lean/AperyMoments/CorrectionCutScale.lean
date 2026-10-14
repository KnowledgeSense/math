import AperyMoments.EllipticNorm
import AperyMoments.CorrectionRightValue

noncomputable section
open Set MeasureTheory
namespace AperyMoments

/-- This real scale fixes the moving elliptic branch point in the correction integral. -/
def correctionCutScale (b : ℝ) (w : ℂ) : ℝ :=
  Real.sqrt ((w.re - b) ^ 2 - w.im ^ 2) / 4

theorem correctionParameter_re (b v : ℝ) (w : ℂ) :
    (correctionParameter b w v).re = ((w.re - b) ^ 2 - w.im ^ 2) * v ^ 2 / 16 := by
  unfold correctionParameter
  rw [pow_two]
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem correctionParameter_im (b v : ℝ) (w : ℂ) :
    (correctionParameter b w v).im = (w.re - b) * w.im * v ^ 2 / 8 := by
  unfold correctionParameter
  rw [pow_two]
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem correctionParameter_re_scale {b : ℝ} {w : ℂ}
    (hw : 0 ≤ (w.re - b) ^ 2 - w.im ^ 2) (v : ℝ) :
    (correctionParameter b w v).re = (correctionCutScale b w * v) ^ 2 := by
  rw [correctionParameter_re]
  unfold correctionCutScale
  rw [mul_pow, div_pow, Real.sq_sqrt hw]
  ring

theorem correctionCutScale_continuous (b : ℝ) : Continuous (correctionCutScale b) := by
  unfold correctionCutScale
  fun_prop

theorem correctionCutScale_ofReal {b w : ℝ} (hw : b ≤ w) :
    correctionCutScale b (w : ℂ) = (w - b) / 4 := by
  simp only [correctionCutScale, Complex.ofReal_re, Complex.ofReal_im, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero,
    Real.sqrt_sq (sub_nonneg.mpr hw)]

/-- The exact real part is below the branch point on the first rescaled interval. -/
theorem correctionParameter_first_re {b : ℝ} {w : ℂ}
    (hw : 0 < (w.re - b) ^ 2 - w.im ^ 2) (v : ℝ) :
    (correctionParameter b w (v / correctionCutScale b w)).re = v ^ 2 := by
  have hA : correctionCutScale b w ≠ 0 := ne_of_gt (by unfold correctionCutScale; positivity)
  rw [correctionParameter_re_scale hw.le]
  congr 1
  field_simp

/-- On the second interval the singularity is fixed at zero. -/
theorem correctionParameter_second_re {b : ℝ} {w : ℂ}
    (hw : 0 < (w.re - b) ^ 2 - w.im ^ 2) (v : ℝ) :
    (correctionParameter b w ((1 + (correctionCutScale b w - 1) * v) / correctionCutScale b w)).re =
      (1 + (correctionCutScale b w - 1) * v) ^ 2 := by
  exact correctionParameter_first_re hw _

end AperyMoments
