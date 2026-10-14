import AperyMoments.CorrectionRadialBound
import AperyMoments.LowerEllipticScaled

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

def correctionWeakBound (b : ℝ) : ℝ :=
  b ^ (-(1 / 2 : ℝ)) * ((8 * (1 / 2 : ℝ) ^ (-(1 / 16 : ℝ))) * weakSingularityBound +
    (Real.pi / 2) * ∫ v in (0 : ℝ)..1, correctionWeight v)

theorem correctionWeakBound_nonneg {b : ℝ} (hb : 0 < b) : 0 ≤ correctionWeakBound b := by
  unfold correctionWeakBound
  have h : 0 ≤ ∫ v in (0 : ℝ)..1, correctionWeight v := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro v hv
    exact Real.rpow_nonneg (sub_nonneg.mpr hv.2) _
  have hn := weakSingularityBound_nonneg
  positivity

theorem correctionBase_norm_bound_right {b : ℝ} {w : ℂ} {v : ℝ}
    (hb : 0 < b) (hw : 0 ≤ w.re) (hv : v ∈ Icc 0 1) :
    ‖correctionBase b w v ^ (-(1 / 2 : ℂ))‖ ≤ b ^ (-(1 / 2 : ℝ)) := by
  apply inverse_sqrt_cpow_bound_re hb
  simp only [correctionBase, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  nlinarith [mul_nonneg hw (sub_nonneg.mpr hv.2), mul_nonneg hb.le hv.1]

theorem correctionWeighted_radial_bound {b : ℝ} {w : ℂ} {v : ℝ}
    (hb : 0 < b) (hw : w.im < 0) (hre : 0 ≤ w.re) (hD : 2 ≤ ‖w - b‖)
    (hv : v ∈ Icc 0 1) (hne : v ≠ (‖w - b‖ / 4)⁻¹) :
    ‖correctionRegular b w v * (correctionWeight v : ℂ)‖ ≤ b ^ (-(1 / 2 : ℝ)) *
      ((8 * (1 / 2 : ℝ) ^ (-(1 / 16 : ℝ))) *
        (‖v - (‖w - b‖ / 4)⁻¹‖ ^ (-(1 / 4 : ℝ)) / 4 + (1 - v) ^ (-(2 / 3 : ℝ)) / (4 / 3)) +
        (Real.pi / 2) * correctionWeight v) := by
  have hk := correctionElliptic_radial_bound (correctionParameter_mem_domain hw hv) hD hv.1 hne
  have hbse := correctionBase_norm_bound_right hb hre hv
  have hwgt : 0 ≤ correctionWeight v := Real.rpow_nonneg (sub_nonneg.mpr hv.2) _
  have hk0 : 0 ≤ (8 * (1 / 2 : ℝ) ^ (-(1 / 16 : ℝ))) *
      ‖v - (‖w - b‖ / 4)⁻¹‖ ^ (-(1 / 16 : ℝ)) + Real.pi / 2 := by positivity
  have hprod := mul_le_mul_of_nonneg_right
    (mul_le_mul hk hbse (norm_nonneg _) hk0) hwgt
  have hy := weak_singularity_weight_bound (a := (‖w - b‖ / 4)⁻¹) hv.2
  have hb0 : 0 ≤ b ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hb.le _
  have hc0 : 0 ≤ 8 * (1 / 2 : ℝ) ^ (-(1 / 16 : ℝ)) := by positivity
  have hy' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy hc0) hb0
  unfold correctionRegular
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwgt]
  unfold correctionWeight at *
  nlinarith [hprod, hy']

theorem correctionIntegral_uniform_bound {b : ℝ} {w : ℂ}
    (hb : 0 < b) (hw : w.im < 0) (hre : 0 ≤ w.re) (hD : 2 ≤ ‖w - b‖) :
    ‖∫ v in (0 : ℝ)..1, correctionRegular b w v * (correctionWeight v : ℂ)‖ ≤ correctionWeakBound b := by
  let a : ℝ := (‖w - b‖ / 4)⁻¹
  let k : ℝ := 8 * (1 / 2 : ℝ) ^ (-(1 / 16 : ℝ))
  have hD0 : 0 < ‖w - b‖ / 4 := by positivity
  have ha0 : 0 ≤ a := (inv_pos.mpr hD0).le
  have ha2 : a ≤ 2 := by
    dsimp [a]
    apply (inv_le_comm₀ hD0 (by norm_num)).mpr
    linarith
  have hi := correctionRegular_weight_integrable hb (Or.inl hw)
  have hm := IntervalIntegrable.const_mul ((IntervalIntegrable.const_mul
    (weakSingularity_majorant_integrable a) k).add
      (IntervalIntegrable.const_mul correctionWeight_integrable (Real.pi / 2))) (b ^ (-(1 / 2 : ℝ)))
  calc
    _ ≤ ∫ v in (0 : ℝ)..1, ‖correctionRegular b w v * (correctionWeight v : ℂ)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ v in (0 : ℝ)..1, b ^ (-(1 / 2 : ℝ)) *
        (k * (‖v - a‖ ^ (-(1 / 4 : ℝ)) / 4 + (1 - v) ^ (-(2 / 3 : ℝ)) / (4 / 3)) +
          (Real.pi / 2) * correctionWeight v) := by
      apply intervalIntegral.integral_mono_ae_restrict (by norm_num) hi.norm hm
      filter_upwards [ae_restrict_of_ae (show ∀ᵐ v : ℝ ∂volume, v ≠ a from by
          apply ae_iff.mpr
          simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton a : volume {a} = 0)), ae_restrict_mem measurableSet_Icc] with v hv hmem
      exact correctionWeighted_radial_bound hb hw hre hD hmem hv
    _ ≤ correctionWeakBound b := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (IntervalIntegrable.const_mul (weakSingularity_majorant_integrable a) k)
          (IntervalIntegrable.const_mul correctionWeight_integrable (Real.pi / 2)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      unfold correctionWeakBound
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hb.le _)
      have hh := mul_le_mul_of_nonneg_left (weakSingularity_majorant_integral_le ha0 ha2)
        (show 0 ≤ k by dsimp [k]; positivity)
      dsimp only [k] at hh
      linarith

/-- A uniform bound through all finite outer branch collisions, including w=b+4. -/
theorem continuedCorrection_uniform_bound {b M : ℝ} {w : ℂ}
    (hb : 0 < b) (hw : w.im < 0) (hre : 0 ≤ w.re)
    (hD : 2 ≤ ‖w - b‖) (hM : ‖w - b‖ ≤ M) :
    ‖continuedCorrection b w‖ ≤ (M / Real.pi) * correctionWeakBound b := by
  have hpow : ‖((b : ℂ) - w) ^ (-(1 / 2 : ℂ))‖ = ‖w - b‖ ^ (-(1 / 2 : ℝ)) := by
    have h := Complex.norm_cpow_real ((b : ℂ) - w) (-(1 / 2 : ℝ))
    simpa only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      norm_sub_rev] using h
  have hp : ‖w - b‖ ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
      (show 1 ≤ ‖w - b‖ by linarith) (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  have hpre : ‖((b : ℂ) - w) * (((b : ℂ) - w) ^ (-(1 / 2 : ℂ))) / (Real.pi : ℂ)‖ ≤ M / Real.pi := by
    rw [norm_div, norm_mul, hpow, norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    apply div_le_div_of_nonneg_right _ Real.pi_pos.le
    calc
      ‖w - b‖ * ‖w - b‖ ^ (-(1 / 2 : ℝ)) ≤ ‖w - b‖ := by nlinarith [norm_nonneg (w - b)]
      _ ≤ M := hM
  unfold continuedCorrection
  rw [norm_mul]
  exact mul_le_mul hpre (correctionIntegral_uniform_bound hb hw hre hD) (norm_nonneg _)
    (div_nonneg (by linarith) Real.pi_pos.le)

end AperyMoments
