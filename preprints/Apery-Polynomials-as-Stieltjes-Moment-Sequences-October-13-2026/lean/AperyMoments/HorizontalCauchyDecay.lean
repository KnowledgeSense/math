import AperyMoments.HorizontalCauchyBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology Interval

theorem cauchy_kernel_norm_bound (F : ℂ→ℂ) (z w : ℂ) (C : ℝ)
    (hC : 0≤C) (hw : 0<‖w‖) (hz : 2*‖z‖≤‖w‖) (hF : ‖F w‖≤C/‖w‖) :
    ‖F w/(w-z)‖≤2*C/‖w‖^2 := by
  have hd : ‖w‖/2≤‖w-z‖ := by
    have h := norm_sub_norm_le w z
    linarith
  rw [norm_div]
  have h := div_le_div₀ (div_nonneg hC (norm_nonneg _)) hF (by positivity : 0<‖w‖/2) hd
  calc _ ≤ (C/‖w‖)/(‖w‖/2) := h
       _ = _ := by field

theorem vertical_bounded_of_decay (F : ℂ→ℂ) (z : ℂ) (C R c d : ℝ)
    (hC : 0≤C) (hc : 0<c) (hcd : c≤d)
    (hF : ∀w:ℂ,0<w.im→R≤‖w‖→‖F w‖≤C/‖w‖) :
    (∀ᶠr:ℝ in atTop,∀y∈Ι c d,‖F ((z.re+r:ℝ)+y*I)‖≤C) ∧
    (∀ᶠr:ℝ in atTop,∀y∈Ι c d,‖F ((z.re-r:ℝ)+y*I)‖≤C) := by
  have hpoint (w:ℂ) (hwim : 0<w.im) (hwn : max R 1≤‖w‖) : ‖F w‖≤C :=
    (hF w hwim ((le_max_left _ _).trans hwn)).trans
      (div_le_self hC ((le_max_right _ _).trans hwn))
  constructor
  · filter_upwards [eventually_ge_atTop (|z.re|+max R 1)] with r hr
    intro y hy
    have hyc : c<y := by simpa only [min_eq_left hcd] using hy.1
    apply hpoint _ (by simpa using hc.trans hyc)
    have h := Complex.re_le_norm (((z.re+r:ℝ)+y*I):ℂ)
    simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero] at h
    linarith [neg_abs_le z.re]
  · filter_upwards [eventually_ge_atTop (|z.re|+max R 1)] with r hr
    intro y hy
    have hyc : c<y := by simpa only [min_eq_left hcd] using hy.1
    apply hpoint _ (by simpa using hc.trans hyc)
    have h := (abs_le.mp (Complex.abs_re_le_norm (((z.re-r:ℝ)+y*I):ℂ))).1
    simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero] at h
    linarith [le_abs_self z.re]

end AperyMoments
