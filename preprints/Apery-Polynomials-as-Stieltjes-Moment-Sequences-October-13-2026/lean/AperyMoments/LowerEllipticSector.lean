import AperyMoments.EllipticRadialBound
import AperyMoments.LowerEllipticNorm

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem norm_affine_sector_lower {z : ℂ} {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hz : -‖z‖ / 2 ≤ z.re) :
    (a + c * ‖z‖) / 2 ≤ ‖(a : ℂ) + (c : ℂ) * z‖ := by
  have hn : ‖(a : ℂ) + (c : ℂ) * z‖ ^ 2 =
      a ^ 2 + 2 * a * c * z.re + c ^ 2 * ‖z‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, zero_add, sub_zero]
    ring
  have hp := mul_nonneg (mul_nonneg ha hc) (show 0 ≤ 2 * z.re + ‖z‖ by linarith)
  have hs := sq_nonneg (a - c * ‖z‖)
  have hN := norm_nonneg ((a : ℂ) + (c : ℂ) * z)
  have hS : 0 ≤ a + c * ‖z‖ := by positivity
  nlinarith

theorem inverse_sqrt_cpow_sector_bound {z : ℂ} {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hz : -‖z‖ / 2 ≤ z.re) (hp : 0 < a + c * ‖z‖) :
    ‖((a : ℂ) + (c : ℂ) * z) ^ (-(1 / 2 : ℂ))‖ ≤
      (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (a + c * ‖z‖) ^ (-(1 / 2 : ℝ)) := by
  have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (a + c * ‖z‖) / 2)
    (norm_affine_sector_lower ha hc hz) (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  have hn := Complex.norm_cpow_real ((a : ℂ) + (c : ℂ) * z) (-(1 / 2 : ℝ))
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hn
  rw [hn]
  have he : (a + c * ‖z‖) / 2 = (1 / 2 : ℝ) * (a + c * ‖z‖) := by ring
  rw [he, Real.mul_rpow (by norm_num) hp.le] at h
  exact h

theorem lowerEllipticKernel_sector_bound {z : ℂ} (hz0 : z ≠ 0)
    (hz : -‖z‖ / 2 ≤ z.re) (t : ℝ) :
    ‖lowerEllipticKernel z t‖ ≤
      ((1 / 2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * ‖lowerEllipticKernel (‖z‖ : ℂ) t‖ := by
  have hR : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have h1 := inverse_sqrt_cpow_sector_bound (sq_nonneg t) (by norm_num : (0 : ℝ) ≤ 1) hz (by positivity)
  have h2 := inverse_sqrt_cpow_sector_bound (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg t) hz (by positivity)
  have he1 : ((t ^ 2 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * z = (t : ℂ) ^ 2 + z := by push_cast; ring
  have he2 : ((1 : ℝ) : ℂ) + ((t ^ 2 : ℝ) : ℂ) * z = 1 + z * (t : ℂ) ^ 2 := by push_cast; ring
  rw [he1] at h1
  rw [he2] at h2
  simp only [one_mul] at h1
  rw [mul_comm (t ^ 2) ‖z‖] at h2
  have hh := mul_le_mul h1 h2 (norm_nonneg _)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
  rw [lowerEllipticKernel_ofReal hR, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ lowerEllipticRealKernel ‖z‖ t by unfold lowerEllipticRealKernel; positivity)]
  unfold lowerEllipticKernel lowerEllipticRealKernel
  rw [norm_mul]
  nlinarith [hh]

theorem lowerEllipticIntegral_sector_bound {z : ℂ} (him : z.im < 0)
    (hz : -‖z‖ / 2 ≤ z.re) :
    ‖lowerEllipticIntegral z‖ ≤ ((1 / 2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * ellipticK (1 - ‖z‖ ^ 2) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at him
  have hR := norm_pos_iff.mpr hz0
  have hi := lowerEllipticKernel_integrableOn_of_first (‖z‖ : ℂ)
    ((rightEllipticKernel_continuous hR).intervalIntegrable 0 1)
  unfold lowerEllipticIntegral
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖lowerEllipticKernel z t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), ((1 / 2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * ‖lowerEllipticKernel (‖z‖ : ℂ) t‖ := by
      apply integral_mono_ae (lowerEllipticKernel_integrable him).integrableOn.norm (hi.norm.const_mul _)
      exact Filter.Eventually.of_forall (lowerEllipticKernel_sector_bound hz0 hz)
    _ = _ := by rw [integral_const_mul, lowerElliptic_positive_norm_integral hR]

end AperyMoments
