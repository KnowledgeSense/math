import AperyMoments.EllipticRayWeighted

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def correctionDecayConstant (b : ℝ) : ℝ :=
  Real.pi⁻¹ * b ^ (-(1 / 2 : ℝ)) * ellipticRayWeightedBound * (4 : ℝ) ^ (7 / 8 : ℝ)

theorem correctionDecayConstant_nonneg {b : ℝ} (hb : 0 < b) : 0 ≤ correctionDecayConstant b := by
  unfold correctionDecayConstant
  have h := ellipticRayWeightedBound_nonneg
  positivity

theorem correction_decay_scalar {D : ℝ} (hD : 0 < D) :
    D * D ^ (-(1 / 2 : ℝ)) * (D / 4) ^ (-(7 / 8 : ℝ)) =
      (4 : ℝ) ^ (7 / 8 : ℝ) * D ^ (-(3 / 8 : ℝ)) := by
  rw [show D / 4 = D * (4 : ℝ)⁻¹ by ring, Real.mul_rpow hD.le (by norm_num), Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4),
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
  have hp : D * D ^ (-(1 / 2 : ℝ)) * D ^ (-(7 / 8 : ℝ)) = D ^ (-(3 / 8 : ℝ)) := by
    conv_lhs => lhs; lhs; rw [← Real.rpow_one D]
    rw [← Real.rpow_add hD, ← Real.rpow_add hD]
    norm_num
  norm_num only [neg_neg]
  calc
    _ = (4 : ℝ) ^ (7 / 8 : ℝ) * (D * D ^ (-(1 / 2 : ℝ)) * D ^ (-(7 / 8 : ℝ))) := by ring
    _ = _ := by rw [hp]

/-- Positive power decay is sufficient for the shrinking Cauchy contour at the moment endpoint. -/
theorem continuedCorrection_decay {b : ℝ} {w : ℂ} (hb : 0 < b) (hw : w.im < 0)
    (hre : 0 ≤ w.re) (hD : 16 ≤ ‖w - b‖) :
    ‖continuedCorrection b w‖ ≤ correctionDecayConstant b * ‖w - b‖ ^ (-(3 / 8 : ℝ)) := by
  let D : ℝ := ‖w - b‖
  let q : ℂ := (w - b) / (D : ℂ)
  have hD0 : 0 < D := by dsimp [D]; linarith
  have hq : q.im < 0 := by
    dsimp [q]
    rw [Complex.div_ofReal_im]
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact div_neg_of_neg_of_pos hw hD0
  have hqn : ‖q‖ = 1 := by
    dsimp [q]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD0]
    exact div_self hD0.ne'
  have hparam (v : ℝ) : q * ((D / 4 * v : ℝ) : ℂ) = (w - b) * (v : ℂ) / 4 := by
    dsimp [q]
    push_cast
    field_simp [show (D : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hD0.ne']
  have hk (v : ℝ) : complexEllipticK (correctionParameter b w v) = ellipticRayKernel q (D / 4 * v) := by
    unfold ellipticRayKernel correctionParameter
    rw [hparam]
  have hi := correctionRegular_weight_integrable hb (Or.inl hw)
  have hA : 4 ≤ D / 4 := by dsimp [D]; linarith
  have hri := ellipticRay_weighted_integrable hq (by positivity : 0 ≤ D / 4)
  have hI : ‖∫ v in (0 : ℝ)..1, correctionRegular b w v * (correctionWeight v : ℂ)‖ ≤
      b ^ (-(1 / 2 : ℝ)) * (ellipticRayWeightedBound * (D / 4) ^ (-(7 / 8 : ℝ))) := by
    calc
      _ ≤ ∫ v in (0 : ℝ)..1, ‖correctionRegular b w v * (correctionWeight v : ℂ)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ v in (0 : ℝ)..1, b ^ (-(1 / 2 : ℝ)) *
          (‖ellipticRayKernel q (D / 4 * v)‖ * correctionWeight v) := by
        apply intervalIntegral.integral_mono_on (by norm_num) hi.norm (IntervalIntegrable.const_mul hri _)
        intro v hv
        have hW : 0 ≤ correctionWeight v := Real.rpow_nonneg (sub_nonneg.mpr hv.2) _
        unfold correctionRegular
        rw [norm_mul, norm_mul, hk, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW]
        have h := mul_le_mul_of_nonneg_left (correctionBase_norm_bound_right hb hre hv)
          (norm_nonneg (ellipticRayKernel q (D / 4 * v)))
        have h' := mul_le_mul_of_nonneg_right h hW
        nlinarith
      _ ≤ _ := by
        rw [intervalIntegral.integral_const_mul]
        exact mul_le_mul_of_nonneg_left (ellipticRay_weighted_bound hq hqn hA) (Real.rpow_nonneg hb.le _)
  have hpre : ‖((b : ℂ) - w) * (((b : ℂ) - w) ^ (-(1 / 2 : ℂ))) / (Real.pi : ℂ)‖ =
      D * D ^ (-(1 / 2 : ℝ)) / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hp := Complex.norm_cpow_real ((b : ℂ) - w) (-(1 / 2 : ℝ))
    simpa only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      norm_sub_rev, D] using congrArg (fun r : ℝ => ‖(b : ℂ) - w‖ * r / Real.pi) hp
  unfold continuedCorrection
  rw [norm_mul, hpre]
  calc
    _ ≤ (D * D ^ (-(1 / 2 : ℝ)) / Real.pi) *
        (b ^ (-(1 / 2 : ℝ)) * (ellipticRayWeightedBound * (D / 4) ^ (-(7 / 8 : ℝ)))) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by
      unfold correctionDecayConstant
      rw [show (D * D ^ (-(1 / 2 : ℝ)) / Real.pi) *
          (b ^ (-(1 / 2 : ℝ)) * (ellipticRayWeightedBound * (D / 4) ^ (-(7 / 8 : ℝ)))) =
          (Real.pi⁻¹ * b ^ (-(1 / 2 : ℝ)) * ellipticRayWeightedBound) *
            (D * D ^ (-(1 / 2 : ℝ)) * (D / 4) ^ (-(7 / 8 : ℝ))) by ring,
        correction_decay_scalar hD0]
      dsimp [D]
      ring

end AperyMoments
