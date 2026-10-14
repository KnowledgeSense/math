import AperyMoments.CorrectionCentral
import AperyMoments.ArcsineConvolution

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem central_correction_change_integrand {b w v : ℝ} (hb : 0 < b)
    (hl : -b < w) (hr : w < b) (hv : v ∈ Ioo 0 1) :
    (b - w) * (ellipticK ((w - (w + (b - w) * v)) ^ 2 / 16) /
      Real.sqrt (b ^ 2 - (w + (b - w) * v) ^ 2)) =
    (b - w) * (b - w) ^ (-(1 / 2 : ℝ)) *
      (ellipticK (((w - b) * v / 4) ^ 2) *
        (b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) * correctionWeight v) := by
  have ha : 0 < b - w := sub_pos.mpr hr
  have hc : 0 < b * (1 + v) + w * (1 - v) := by
    have := mul_pos (by linarith : 0 < b + w) (by linarith [hv.2] : 0 < 1 - v)
    nlinarith [mul_pos hb hv.1]
  have hd : 0 < 1 - v := by linarith [hv.2]
  have he : b ^ 2 - (w + (b - w) * v) ^ 2 =
      ((b - w) * (1 - v)) * (b * (1 + v) + w * (1 - v)) := by ring
  have hp : (w - (w + (b - w) * v)) ^ 2 / 16 = (((w - b) * v / 4) ^ 2) := by ring
  rw [hp, div_eq_mul_inv, ← inverse_sqrt_rpow (by rw [he]; positivity), he,
    Real.mul_rpow (mul_nonneg ha.le hd.le) hc.le, Real.mul_rpow ha.le (by linarith [hv.2])]
  unfold correctionWeight
  ring

/-- The central real correction is the original arcsine-weighted segment integral. -/
theorem centralCorrection_eq_realIntegral {b w : ℝ} (hb : 0 < b)
    (hl : -b < w) (hr : w < b) :
    centralCorrection b w = Real.pi⁻¹ * ∫ u in w..b,
      ellipticK ((w - u) ^ 2 / 16) / Real.sqrt (b ^ 2 - u ^ 2) := by
  have he := intervalIntegral.smul_integral_comp_add_mul
    (a := (0 : ℝ)) (b := 1)
    (fun u : ℝ => ellipticK ((w - u) ^ 2 / 16) / Real.sqrt (b ^ 2 - u ^ 2)) (b - w) w
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one, add_sub_cancel] at he
  rw [← he, ← intervalIntegral.integral_const_mul]
  have hi : (∫ v in (0 : ℝ)..1, (b - w) *
      (ellipticK ((w - (w + (b - w) * v)) ^ 2 / 16) /
        Real.sqrt (b ^ 2 - (w + (b - w) * v) ^ 2))) =
      (b - w) * (b - w) ^ (-(1 / 2 : ℝ)) *
        ∫ v in (0 : ℝ)..1, ellipticK (((w - b) * v / 4) ^ 2) *
          (b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) * correctionWeight v := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hne : ∀ᵐ v : ℝ ∂volume, v ≠ 1 := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton (1 : ℝ) : volume {(1 : ℝ)} = 0)
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hne] with v hv hv1
    exact central_correction_change_integrand hb hl hr ⟨hv.1, lt_of_le_of_ne hv.2 hv1⟩
  rw [hi]
  unfold centralCorrection
  ring

/-- The correction equals precisely the angular contribution where the lattice argument is negative. -/
theorem centralCorrection_eq_angular {b w : ℝ} (hb : 0 < b)
    (hl : -b < w) (hr : w < b) :
    centralCorrection b w = Real.pi⁻¹ * ∫ θ in (0 : ℝ)..Real.pi,
      (Ioi w).indicator (fun u => ellipticK ((w - u) ^ 2 / 16)) (b * Real.cos θ) := by
  rw [centralCorrection_eq_realIntegral hb hl hr, ← arcsine_integral_substitution_real hb]
  congr 1
  rw [intervalIntegral.integral_of_le hr.le, integral_Ioc_eq_integral_Ioo]
  have hi : (fun u : ℝ => (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ *
      (Ioi w).indicator (fun u => ellipticK ((w - u) ^ 2 / 16)) u) =
      (Ioi w).indicator (fun u => ellipticK ((w - u) ^ 2 / 16) /
        Real.sqrt (b ^ 2 - u ^ 2)) := by
    funext u
    by_cases hu : u ∈ Ioi w <;> simp [hu, div_eq_mul_inv, mul_comm]
  rw [hi, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have hs : Ioi w ∩ Ioo (-b) b = Ioo w b := by
    ext u
    simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨hu, hu'⟩
      exact ⟨hu, hu'.2⟩
    · intro hu
      exact ⟨hu.1, lt_trans hl hu.1, hu.2⟩
  rw [hs]

end AperyMoments
