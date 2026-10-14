import AperyMoments.EllipticConnection
import AperyMoments.EllipticBounds

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem inverse_sqrt_cpow_norm_re_im (a : ℝ) :
    ‖(a : ℂ) ^ (-(1 / 2 : ℂ))‖ =
      ((a : ℂ) ^ (-(1 / 2 : ℂ))).re - ((a : ℂ) ^ (-(1 / 2 : ℂ))).im := by
  by_cases ha : 0 ≤ a
  · rw [inverse_sqrt_cpow_of_nonneg ha]
    simp only [Complex.norm_real, Complex.ofReal_re, Complex.ofReal_im, sub_zero, Real.norm_eq_abs]
    exact abs_of_nonneg (Real.rpow_nonneg ha _)
  · have hneg : a < 0 := lt_of_not_ge ha
    rw [inverse_sqrt_cpow_of_neg hneg]
    simp [Complex.norm_real, Real.norm_eq_abs]
    exact Real.rpow_nonneg (by linarith) _

theorem norm_inverse_sqrt_cpow_real (a : ℝ) :
    ‖(a : ℂ) ^ (-(1 / 2 : ℂ))‖ = ‖a‖ ^ (-(1 / 2 : ℝ)) := by
  simpa only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.norm_real] using Complex.norm_cpow_real (a : ℂ) (-(1 / 2 : ℝ))

theorem elliptic_cut_majorant_integral {m : ℝ} (hm : 1 < m) :
    (∫ θ in (0 : ℝ)..Real.pi / 2, ‖1 - m * Real.sin θ ^ 2‖ ^ (-(1 / 2 : ℝ))) =
      m ^ (-(1 / 2 : ℝ)) * ellipticK m⁻¹ + ellipticK (1 - m) := by
  let f : ℝ → ℂ := fun θ => (1 - (m : ℂ) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))
  have hi := complexEllipticK_cut_integrable hm
  have he θ : ‖1 - m * Real.sin θ ^ 2‖ ^ (-(1 / 2 : ℝ)) = RCLike.re (f θ) - RCLike.im (f θ) := by
    rw [← norm_inverse_sqrt_cpow_real, inverse_sqrt_cpow_norm_re_im]
    have hbase : ((1 - m * Real.sin θ ^ 2 : ℝ) : ℂ) = 1 - (m : ℂ) * (Real.sin θ : ℂ) ^ 2 := by push_cast; rfl
    rw [hbase]
    rfl
  have hire : IntegrableOn f (Ioc 0 (Real.pi / 2)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp hi
  simp_rw [he]
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2),
    integral_sub hire.re hire.im, integral_re hire, integral_im hire,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  change (complexEllipticK (m : ℂ)).re - (complexEllipticK (m : ℂ)).im = _
  rw [complexEllipticK_cut_value hm]
  simp

theorem complexEllipticK_vertical_norm_bound_above {m ε : ℝ} (hm : 1 < m) (hε : 0 < ε) :
    ‖complexEllipticK ((m : ℂ) - Complex.I * ε)‖ ≤
      m ^ (-(1 / 2 : ℝ)) * ellipticK m⁻¹ + ellipticK (1 - m) := by
  have hz : (m : ℂ) - Complex.I * ε ∈ ellipticDomain := by
    left
    simpa using (neg_neg_of_pos hε).ne
  have hi := (complexEllipticK_integrand_continuous hz).intervalIntegrable (μ := volume) 0 (Real.pi / 2)
  unfold complexEllipticK
  calc
    _ ≤ ∫ θ in (0 : ℝ)..Real.pi / 2,
        ‖(1 - ((m : ℂ) - Complex.I * ε) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by positivity)
    _ ≤ ∫ θ in (0 : ℝ)..Real.pi / 2, ‖1 - m * Real.sin θ ^ 2‖ ^ (-(1 / 2 : ℝ)) := by
      apply intervalIntegral.integral_mono_ae_restrict (by positivity) hi.norm (elliptic_cut_majorant_intervalIntegrable hm _ _)
      filter_upwards [ae_restrict_of_ae (elliptic_cut_ae_nonzero hm), ae_restrict_mem measurableSet_Icc] with θ hθ hmem
      exact elliptic_vertical_integrand_bound m ε θ (hθ hmem)
    _ = _ := elliptic_cut_majorant_integral hm

theorem complexEllipticK_vertical_norm_bound_below {m : ℝ} (hm : m < 1) (ε : ℝ) :
    ‖complexEllipticK ((m : ℂ) - Complex.I * ε)‖ ≤ ellipticK m := by
  have hz : (m : ℂ) - Complex.I * ε ∈ ellipticDomain := by right; simpa using hm
  have hi := (complexEllipticK_integrand_continuous hz).intervalIntegrable (μ := volume) 0 (Real.pi / 2)
  unfold complexEllipticK ellipticK
  calc
    _ ≤ ∫ θ in (0 : ℝ)..Real.pi / 2,
        ‖(1 - ((m : ℂ) - Complex.I * ε) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by positivity)
    _ ≤ _ := by
      apply intervalIntegral.integral_mono (by positivity) hi.norm (ellipticK_integrable hm)
      intro θ
      have hbase := ellipticK_base_pos hm θ
      simpa [Real.norm_eq_abs, abs_of_pos hbase] using elliptic_vertical_integrand_bound m ε θ hbase.ne'

theorem ellipticK_elementary_bound {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    ellipticK m ≤ (Real.pi / 2) * (1 - m) ^ (-(1 / 2 : ℝ)) := by
  unfold ellipticK
  calc
    _ ≤ ∫ _θ in (0 : ℝ)..Real.pi / 2, (1 - m) ^ (-(1 / 2 : ℝ)) := by
      apply intervalIntegral.integral_mono (by positivity) (ellipticK_integrable hm1) intervalIntegrable_const
      intro θ
      apply Real.rpow_le_rpow_of_nonpos (by linarith : 0 < 1 - m)
      · nlinarith [Real.sin_sq_le_one θ]
      · norm_num
    _ = _ := by simp

theorem ellipticK_cut_elementary_bound {m : ℝ} (hm : 1 < m) :
    m ^ (-(1 / 2 : ℝ)) * ellipticK m⁻¹ + ellipticK (1 - m) ≤
      (Real.pi / 2) * ((m - 1) ^ (-(1 / 2 : ℝ)) + 1) := by
  have hm0 : 0 < m := by linarith
  have hmi : m⁻¹ < 1 := (inv_lt_one₀ hm0).mpr hm
  have hp := ellipticK_elementary_bound (inv_nonneg.mpr hm0.le) hmi
  have hscale := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hm0.le (-(1 / 2 : ℝ)))
  have he : m ^ (-(1 / 2 : ℝ)) * (1 - m⁻¹) ^ (-(1 / 2 : ℝ)) =
      (m - 1) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.mul_rpow hm0.le (by linarith : 0 ≤ 1 - m⁻¹)]
    congr 1
    field_simp
  have hlow := ellipticK_mono (show 1 - m ≤ 0 by linarith) (by norm_num : (0 : ℝ) < 1)
  rw [ellipticK_zero] at hlow
  have he' : m ^ (-(1 / 2 : ℝ)) * ((Real.pi / 2) * (1 - m⁻¹) ^ (-(1 / 2 : ℝ))) =
      (Real.pi / 2) * (m - 1) ^ (-(1 / 2 : ℝ)) := by rw [← he]; ring
  rw [he'] at hscale
  linarith

theorem complexEllipticK_re_bound_below {z : ℂ} (hz : z.re < 1) :
    ‖complexEllipticK z‖ ≤ ellipticK z.re := by
  have h := complexEllipticK_vertical_norm_bound_below hz (-z.im)
  have he : (z.re : ℂ) - Complex.I * (-z.im : ℝ) = z := by apply Complex.ext <;> simp
  rwa [he] at h

theorem complexEllipticK_re_bound_above {z : ℂ} (hz : z.im < 0) (hre : 1 < z.re) :
    ‖complexEllipticK z‖ ≤ (Real.pi / 2) * ((z.re - 1) ^ (-(1 / 2 : ℝ)) + 1) := by
  have h := complexEllipticK_vertical_norm_bound_above hre (neg_pos.mpr hz)
  have he : (z.re : ℂ) - Complex.I * (-z.im : ℝ) = z := by apply Complex.ext <;> simp
  rw [he] at h
  exact h.trans (ellipticK_cut_elementary_bound hre)

end AperyMoments
