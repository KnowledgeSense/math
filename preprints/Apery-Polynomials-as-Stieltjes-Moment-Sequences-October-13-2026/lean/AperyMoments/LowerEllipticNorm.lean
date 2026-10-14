import AperyMoments.LowerEllipticLimit
import AperyMoments.EllipticBounds
import AperyMoments.LowerEllipticRight

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem lowerEllipticKernel_negative_norm {c t : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (ht : 0 < t) :
    ‖lowerEllipticKernel (-c) t‖ = (lowerEllipticKernel (-c) t).re -
      (lowerEllipticKernel (-c) t).im := by
  have hphase (a : ℝ) (ha : 0 ≤ a) : ‖-Complex.I * (a : ℂ)‖ =
      (-Complex.I * (a : ℂ)).re - (-Complex.I * (a : ℂ)).im := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  have hreal (a : ℝ) (ha : 0 ≤ a) : ‖(a : ℂ)‖ = (a : ℂ).re - (a : ℂ).im := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  by_cases hfirst : t ≤ Real.sqrt c
  · rw [lowerEllipticKernel_negative_first hc hc1 ⟨ht.le, hfirst⟩]
    apply hphase
    have ht2 : t ^ 2 ≤ c := by nlinarith [Real.sq_sqrt hc.le, Real.sqrt_nonneg c]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by nlinarith) _)
  · by_cases hmid : t ≤ (Real.sqrt c)⁻¹
    · rw [lowerEllipticKernel_negative_middle hc ⟨(lt_of_not_ge hfirst).le, hmid⟩]
      apply hreal
      have hs := Real.sqrt_pos.2 hc
      have hst : Real.sqrt c * t ≤ 1 := by
        simpa only [mul_inv_cancel₀ hs.ne'] using mul_le_mul_of_nonneg_left hmid hs.le
      have he : (Real.sqrt c * t) ^ 2 = c * t ^ 2 := by rw [mul_pow, Real.sq_sqrt hc.le]
      exact mul_nonneg (Real.rpow_nonneg (by nlinarith [Real.sq_sqrt hc.le]) _)
        (Real.rpow_nonneg (by nlinarith [mul_pos hs ht]) _)
    · rw [lowerEllipticKernel_negative_tail hc hc1 (lt_of_not_ge hmid)]
      apply hphase
      have hh := elliptic_tail_bases_pos hc hc1 (lt_of_not_ge hmid)
      exact mul_nonneg (Real.rpow_nonneg hh.2.le _) (Real.rpow_nonneg hh.1.le _)

theorem lowerElliptic_negative_norm_integral {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    (∫ t in Ioi (0 : ℝ), ‖lowerEllipticKernel (-c) t‖) =
      ellipticK (1 - c ^ 2) + 2 * ellipticK (c ^ 2) := by
  have hi := lowerElliptic_negative_integrable hc hc1
  calc
    _ = ∫ t in Ioi (0 : ℝ), (lowerEllipticKernel (-c) t).re -
        (lowerEllipticKernel (-c) t).im :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => lowerEllipticKernel_negative_norm hc hc1 ht
    _ = _ := by
      change (∫ t in Ioi (0 : ℝ), RCLike.re (lowerEllipticKernel (-c) t) -
        RCLike.im (lowerEllipticKernel (-c) t)) = _
      rw [integral_sub hi.re hi.im, integral_re hi, integral_im hi]
      change (lowerEllipticIntegral (-c)).re - (lowerEllipticIntegral (-c)).im = _
      rw [lowerEllipticIntegral_negative_value hc hc1]
      simp

theorem lowerEllipticIntegral_negative_vertical_norm_bound {c ε : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (hε : 0 < ε) :
    ‖lowerEllipticIntegral (-(c : ℂ) - Complex.I * ε)‖ ≤
      ellipticK (1 - c ^ 2) + 2 * ellipticK (c ^ 2) := by
  have hz : (-(c : ℂ) - Complex.I * ε).im < 0 := by simpa using neg_neg_of_pos hε
  have hi := lowerElliptic_negative_integrable hc hc1
  unfold lowerEllipticIntegral
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖lowerEllipticKernel (-(c : ℂ) - Complex.I * ε) t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖lowerEllipticKernel (-c) t‖ := by
      apply integral_mono_ae (lowerEllipticKernel_integrable hz).integrableOn.norm hi.norm
      filter_upwards [lowerEllipticKernel_negative_ae_nonzero hc] with t ht
      exact lowerEllipticKernel_negative_vertical_bound c ε t ht.1 ht.2
    _ = _ := lowerElliptic_negative_norm_integral hc hc1

theorem lowerElliptic_positive_norm_integral {c : ℝ} (hc : 0 < c) :
    (∫ t in Ioi (0 : ℝ), ‖lowerEllipticKernel (c : ℂ) t‖) =
      ellipticK (1 - c ^ 2) := by
  have hi := lowerEllipticKernel_integrableOn_of_first (c : ℂ)
    ((rightEllipticKernel_continuous hc).intervalIntegrable 0 1)
  have he : (fun t : ℝ => ‖lowerEllipticKernel (c : ℂ) t‖) =
      (fun t : ℝ => RCLike.re (lowerEllipticKernel (c : ℂ) t)) := by
    funext t
    rw [lowerEllipticKernel_ofReal hc]
    have hnonneg : 0 ≤ lowerEllipticRealKernel c t := by
      unfold lowerEllipticRealKernel
      positivity
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [he, integral_re hi]
  change (lowerEllipticIntegral (c : ℂ)).re = _
  rw [lowerEllipticIntegral_ofReal hc]
  rfl

theorem lowerEllipticIntegral_positive_vertical_norm_bound {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) :
    ‖lowerEllipticIntegral ((c : ℂ) - Complex.I * ε)‖ ≤
      ellipticK (1 - c ^ 2) := by
  have hz : ((c : ℂ) - Complex.I * ε).im < 0 := by simpa using neg_neg_of_pos hε
  have hi := lowerEllipticKernel_integrableOn_of_first (c : ℂ)
    ((rightEllipticKernel_continuous hc).intervalIntegrable 0 1)
  unfold lowerEllipticIntegral
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖lowerEllipticKernel ((c : ℂ) - Complex.I * ε) t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖lowerEllipticKernel (c : ℂ) t‖ := by
      apply integral_mono_ae (lowerEllipticKernel_integrable hz).integrableOn.norm hi.norm
      apply Filter.Eventually.of_forall
      intro t
      simpa using lowerEllipticKernel_negative_vertical_bound (-c) ε t
        (by nlinarith [sq_nonneg t] : t ^ 2 - -c ≠ 0)
        (by nlinarith [mul_nonneg hc.le (sq_nonneg t)] : 1 - -c * t ^ 2 ≠ 0)
    _ = _ := lowerElliptic_positive_norm_integral hc

end AperyMoments
