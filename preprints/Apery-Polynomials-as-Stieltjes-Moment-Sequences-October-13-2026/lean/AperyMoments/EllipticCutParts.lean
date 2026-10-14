import AperyMoments.EllipticCut

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem real_cpow_measurable (p : ℂ) : Measurable (fun a : ℝ => (a : ℂ) ^ p) := by
  apply measurable_of_continuousOn_compl_singleton (0 : ℝ)
  intro a ha
  exact (Complex.continuousAt_ofReal_cpow_const a p (Or.inr ha)).continuousWithinAt

theorem complexEllipticK_cut_integrable {m : ℝ} (hm : 1 < m) :
    IntervalIntegrable (fun θ : ℝ =>
      (1 - (m : ℂ) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) volume 0 (Real.pi / 2) := by
  have he θ : (1 - (m : ℂ) * (Real.sin θ : ℂ) ^ 2) = ((1 - m * Real.sin θ ^ 2 : ℝ) : ℂ) := by
    push_cast; rfl
  have hmeas : Measurable (fun θ : ℝ =>
      (1 - (m : ℂ) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) := by
    simp_rw [he]
    exact (real_cpow_measurable _).comp (by fun_prop)
  apply (elliptic_cut_majorant_intervalIntegrable hm 0 (Real.pi / 2)).mono_fun hmeas.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun θ => by
    dsimp only
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    have h := Complex.norm_cpow_real (1 - (m : ℂ) * (Real.sin θ : ℂ) ^ 2) (-(1 / 2 : ℝ))
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
    rw [h, he, Complex.norm_real]

theorem inverse_sqrt_cpow_of_nonneg {a : ℝ} (ha : 0 ≤ a) :
    (a : ℂ) ^ (-(1 / 2 : ℂ)) = ((a ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have h := Complex.ofReal_cpow ha (-(1 / 2 : ℝ))
  push_cast at h
  exact h.symm

theorem inverse_sqrt_cpow_of_neg {a : ℝ} (ha : a < 0) :
    (a : ℂ) ^ (-(1 / 2 : ℂ)) = -Complex.I * (((-a) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have h := Complex.cpow_ofReal (a : ℂ) (-(1 / 2 : ℝ))
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_neg ha, Complex.arg_ofReal_of_neg ha] at h
  rw [show Real.pi * (-(1 / 2 : ℝ)) = -(Real.pi / 2) by ring,
    Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg, Real.sin_pi_div_two] at h
  simpa [mul_comm] using h

theorem inverse_sqrt_cpow_re (a : ℝ) :
    ((a : ℂ) ^ (-(1 / 2 : ℂ))).re =
      if 0 ≤ a then a ^ (-(1 / 2 : ℝ)) else 0 := by
  split_ifs with ha
  · rw [inverse_sqrt_cpow_of_nonneg ha, Complex.ofReal_re]
  · rw [inverse_sqrt_cpow_of_neg (lt_of_not_ge ha)]
    simp

theorem inverse_sqrt_cpow_im (a : ℝ) :
    ((a : ℂ) ^ (-(1 / 2 : ℂ))).im =
      if 0 ≤ a then 0 else -((-a) ^ (-(1 / 2 : ℝ))) := by
  split_ifs with ha
  · rw [inverse_sqrt_cpow_of_nonneg ha, Complex.ofReal_im]
  · rw [inverse_sqrt_cpow_of_neg (lt_of_not_ge ha)]
    simp

theorem complexEllipticK_cut_re {m : ℝ} (hm : 1 < m) :
    (complexEllipticK m).re = ∫ θ in (0:ℝ)..Real.pi / 2,
      if 0 ≤ 1 - m * Real.sin θ ^ 2 then (1 - m * Real.sin θ ^ 2) ^ (-(1 / 2 : ℝ)) else 0 := by
  change Complex.reCLM (complexEllipticK m) = _
  rw [complexEllipticK, ← Complex.reCLM.intervalIntegral_comp_comm (complexEllipticK_cut_integrable hm)]
  apply intervalIntegral.integral_congr
  intro θ _
  change ((1 - (m : ℂ) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))).re = _
  rw [show 1 - (m : ℂ) * (Real.sin θ : ℂ) ^ 2 = ((1 - m * Real.sin θ ^ 2 : ℝ) : ℂ) by push_cast; rfl]
  exact inverse_sqrt_cpow_re _

theorem complexEllipticK_cut_im {m : ℝ} (hm : 1 < m) :
    (complexEllipticK m).im = ∫ θ in (0:ℝ)..Real.pi / 2,
      if 0 ≤ 1 - m * Real.sin θ ^ 2 then 0 else -((m * Real.sin θ ^ 2 - 1) ^ (-(1 / 2 : ℝ))) := by
  change Complex.imCLM (complexEllipticK m) = _
  rw [complexEllipticK, ← Complex.imCLM.intervalIntegral_comp_comm (complexEllipticK_cut_integrable hm)]
  apply intervalIntegral.integral_congr
  intro θ _
  change ((1 - (m : ℂ) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))).im = _
  rw [show 1 - (m : ℂ) * (Real.sin θ : ℂ) ^ 2 = ((1 - m * Real.sin θ ^ 2 : ℝ) : ℂ) by push_cast; rfl]
  rw [inverse_sqrt_cpow_im, show -(1 - m * Real.sin θ ^ 2) = m * Real.sin θ ^ 2 - 1 by ring]

end AperyMoments
