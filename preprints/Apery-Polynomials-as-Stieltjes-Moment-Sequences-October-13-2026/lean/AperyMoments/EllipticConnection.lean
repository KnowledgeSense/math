import AperyMoments.EllipticCutIntervals
import AperyMoments.ArcsineSubstitution
import AperyMoments.EllipticTransformation
import AperyMoments.EllipticConjugation

noncomputable section
open Set MeasureTheory
namespace AperyMoments

/-- The positive real part of the elliptic branch-cut value, in parameter convention. -/
theorem complexEllipticK_cut_real_connection {m : ℝ} (hm : 1 < m) :
    (complexEllipticK m).re = m ^ (-(1 / 2 : ℝ)) * ellipticK m⁻¹ := by
  have hm0 : 0 < m := by linarith
  have hr := Real.sqrt_pos.mpr hm0
  have h1 : 1 < Real.sqrt m := by nlinarith [Real.sq_sqrt hm0.le]
  have hk0 := inv_pos.mpr hr
  have hk1 := (inv_lt_one₀ hr).mpr h1
  have h := arcsine_substitution_positive hk0 hk1
  have he (θ : ℝ) : Real.sin θ ^ 2 / ((Real.sqrt m)⁻¹) ^ 2 = m * Real.sin θ ^ 2 := by
    rw [div_eq_mul_inv, inv_pow, inv_inv, Real.sq_sqrt hm0.le, mul_comm]
  simp_rw [he] at h
  rw [complexEllipticK_cut_re_interval hm]
  change (∫ θ in (0:ℝ)..Real.arcsin (Real.sqrt m)⁻¹,
    (1 - m * Real.sin θ ^ 2) ^ (-(1 / 2 : ℝ))) = _
  rw [h, inv_pow, Real.sq_sqrt hm0.le, inverse_sqrt_rpow hm0.le]

theorem inverse_sqrt_cpow_im_neg_mul {c : ℝ} (hc : 0 < c) (b : ℝ) :
    (((-c * b : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))).im =
      -(c ^ (-(1 / 2 : ℝ))) * ((b : ℂ) ^ (-(1 / 2 : ℂ))).re := by
  rw [inverse_sqrt_cpow_im, inverse_sqrt_cpow_re]
  by_cases hb : 0 ≤ b
  · by_cases hb0 : b = 0
    · subst b
      norm_num
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hn : ¬0 ≤ -c * b := not_le.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hbp)
      rw [ite_eq_right hn, ite_eq_left hb, show -(-c * b) = c * b by ring,
        Real.mul_rpow hc.le hb]
      ring
  · have hn : 0 ≤ -c * b := mul_nonneg_of_nonpos_of_nonpos (by linarith) (le_of_not_ge hb)
    rw [ite_eq_left hn, ite_eq_right hb, mul_zero]

 theorem complexEllipticK_cut_im_parameter_relation {m : ℝ} (hm : 1 < m) :
    (complexEllipticK m).im = -((m - 1) ^ (-(1 / 2 : ℝ))) *
      (complexEllipticK ((m / (m - 1) : ℝ) : ℂ)).re := by
  have hc : 0 < m - 1 := by linarith
  have hμ : 1 < m / (m - 1) := (lt_div_iff₀ hc).mpr (by linarith)
  let g : ℝ → ℝ := fun θ =>
    ((1 - ((m / (m - 1) : ℝ) : ℂ) * (Real.sin θ : ℂ)^2) ^ (-(1/2:ℂ))).re
  have hr : (∫ θ in (0:ℝ)..Real.pi/2, g θ) = (complexEllipticK ((m/(m-1) : ℝ) : ℂ)).re :=
    Complex.reCLM.intervalIntegral_comp_comm (complexEllipticK_cut_integrable hμ)
  have hs : (∫ θ in (0:ℝ)..Real.pi/2, g (Real.pi/2-θ)) = ∫ θ in (0:ℝ)..Real.pi/2, g θ := by
    simpa only [sub_self, sub_zero] using
      intervalIntegral.integral_comp_sub_left g (a := 0) (b := Real.pi/2) (Real.pi/2)
  change Complex.imCLM (complexEllipticK m) = _
  rw [complexEllipticK, ← Complex.imCLM.intervalIntegral_comp_comm (complexEllipticK_cut_integrable hm)]
  calc
    _ = ∫ θ in (0:ℝ)..Real.pi/2, -((m-1)^(-(1/2:ℝ))) * g (Real.pi/2-θ) := by
      apply intervalIntegral.integral_congr
      intro θ _
      have he : 1 - m * Real.sin θ ^ 2 =
          -(m-1) * (1 - (m/(m-1)) * Real.sin (Real.pi/2-θ)^2) := by
        rw [Real.sin_pi_div_two_sub]
        have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
        rw [hs]
        field_simp [hc.ne']
        ring
      have h := inverse_sqrt_cpow_im_neg_mul hc
        (1 - (m/(m-1)) * Real.sin (Real.pi/2-θ)^2)
      rw [← he] at h
      dsimp [g]
      convert h using 1 <;> push_cast <;> rfl
    _ = -((m-1)^(-(1/2:ℝ))) * (complexEllipticK ((m/(m-1) : ℝ) : ℂ)).re := by
      rw [intervalIntegral.integral_const_mul, hs, hr]

 theorem complexEllipticK_cut_imaginary_connection {m : ℝ} (hm : 1 < m) :
    (complexEllipticK m).im = -ellipticK (1 - m) := by
  have hc : 0 < m - 1 := by linarith
  have hm0 : 0 < m := by linarith
  have hμ : 1 < m / (m - 1) := (lt_div_iff₀ hc).mpr (by linarith)
  rw [complexEllipticK_cut_im_parameter_relation hm, complexEllipticK_cut_real_connection hμ]
  have ht := ellipticK_parameter_transform (m := 1-m) (by linarith)
  have he : 1-(1-m) = m := by ring
  have hp : (1-m)/(1-m-1) = (m/(m-1))⁻¹ := by field_simp [hm0.ne', hc.ne']; ring
  rw [he, hp] at ht
  rw [ht]
  have hprod : (m-1)^(-(1/2:ℝ)) * (m/(m-1))^(-(1/2:ℝ)) = m^(-(1/2:ℝ)) := by
    rw [← Real.mul_rpow hc.le (div_nonneg hm0.le hc.le)]
    congr 1
    field_simp [hc.ne']
  rw [← hprod]
  ring

/-- The complete lower-lip connection formula, with its imaginary sign fixed. -/
theorem complexEllipticK_cut_value {m : ℝ} (hm : 1 < m) :
    complexEllipticK m = ((m ^ (-(1/2:ℝ)) * ellipticK m⁻¹ : ℝ) : ℂ) -
      Complex.I * (ellipticK (1-m) : ℂ) := by
  apply Complex.ext
  · simpa using complexEllipticK_cut_real_connection hm
  · simpa using complexEllipticK_cut_imaginary_connection hm

/-- The upper-minus-lower jump used by the continuation argument. -/
theorem complexEllipticK_cut_jump {m : ℝ} (hm : 1 < m) :
    starRingEnd ℂ (complexEllipticK m) - complexEllipticK m =
      2 * Complex.I * (ellipticK (1-m) : ℂ) := by
  rw [complexEllipticK_cut_value hm]
  apply Complex.ext <;> simp
  ring

end AperyMoments
