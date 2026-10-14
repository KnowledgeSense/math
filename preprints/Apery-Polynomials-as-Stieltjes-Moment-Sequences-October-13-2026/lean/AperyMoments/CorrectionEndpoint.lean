import AperyMoments.CorrectionDecay

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def correctionEndpointConstant (b : ℝ) : ℝ :=
  Real.pi⁻¹ * ellipticK (1 / 2) * b ^ (-(1 / 2 : ℝ)) *
    ∫ v in (0 : ℝ)..1, correctionWeight v

theorem correctionEndpointConstant_nonneg {b : ℝ} (hb : 0 < b) : 0 ≤ correctionEndpointConstant b := by
  have hK := ellipticK_pos (by norm_num : (1 / 2 : ℝ) < 1)
  have hW : 0 ≤ ∫ v in (0 : ℝ)..1, correctionWeight v := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro v hv
    exact Real.rpow_nonneg (sub_nonneg.mpr hv.2) _
  unfold correctionEndpointConstant
  positivity

theorem continuedCorrection_endpoint_bound {b : ℝ} {w : ℂ} (hb : 0 < b)
    (him : w.im < 0) (hre : 0 ≤ w.re) (hD : ‖w - b‖ ≤ 2) :
    ‖continuedCorrection b w‖ ≤ correctionEndpointConstant b * ‖w - b‖ ^ (1 / 2 : ℝ) := by
  have hD0 : 0 < ‖w - b‖ := by
    apply norm_pos_iff.mpr
    intro he
    have h := congrArg Complex.im he
    simp at h
    linarith
  have hi := correctionRegular_weight_integrable hb (Or.inl him)
  have hI : ‖∫ v in (0 : ℝ)..1, correctionRegular b w v * (correctionWeight v : ℂ)‖ ≤
      (ellipticK (1 / 2) * b ^ (-(1 / 2 : ℝ))) * ∫ v in (0 : ℝ)..1, correctionWeight v := by
    calc
      _ ≤ ∫ v in (0 : ℝ)..1, ‖correctionRegular b w v * (correctionWeight v : ℂ)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ v in (0 : ℝ)..1, (ellipticK (1 / 2) * b ^ (-(1 / 2 : ℝ))) * correctionWeight v := by
        apply intervalIntegral.integral_mono_on (by norm_num) hi.norm
          (IntervalIntegrable.const_mul correctionWeight_integrable _)
        intro v hv
        have hm : ‖correctionParameter b w v‖ ≤ 1 / 2 := by
          rw [correctionParameter_norm b w hv.1]
          have hmul : 0 ≤ ‖w - b‖ * v ∧ ‖w - b‖ * v ≤ 2 :=
            ⟨mul_nonneg (norm_nonneg _) hv.1, by nlinarith [mul_le_mul_of_nonneg_left hv.2 (norm_nonneg (w - b))]⟩
          nlinarith
        have hK := (complexEllipticK_radial_norm_bound_below (correctionParameter_mem_domain him hv)
          (by linarith : ‖correctionParameter b w v‖ < 1)).trans
          (ellipticK_mono hm (by norm_num : (1 / 2 : ℝ) < 1))
        have hB := correctionBase_norm_bound_right hb hre hv
        have hW : 0 ≤ correctionWeight v := Real.rpow_nonneg (sub_nonneg.mpr hv.2) _
        unfold correctionRegular
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hK hB (norm_nonneg _) (ellipticK_pos (by norm_num : (1 / 2 : ℝ) < 1)).le) hW
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hp : ‖w - b‖ * ‖w - b‖ ^ (-(1 / 2 : ℝ)) = ‖w - b‖ ^ (1 / 2 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one ‖w - b‖]
    rw [← Real.rpow_add hD0]
    norm_num
  have hcp := Complex.norm_cpow_real ((b : ℂ) - w) (-(1 / 2 : ℝ))
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    norm_sub_rev] at hcp
  unfold continuedCorrection
  rw [norm_mul, norm_div, norm_mul, hcp, norm_sub_rev, hp, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have h := mul_le_mul_of_nonneg_left hI (by positivity : 0 ≤ ‖w - b‖ ^ (1 / 2 : ℝ) / Real.pi)
  unfold correctionEndpointConstant
  convert h using 1; ring

end AperyMoments
