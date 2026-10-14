import AperyMoments.EllipticMildBound

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem elliptic_radial_integrand_bound (z : ℂ) (θ : ℝ)
    (hne : 1 - ‖z‖ * Real.sin θ ^ 2 ≠ 0) :
    ‖(1 - z * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤
      ‖1 - ‖z‖ * Real.sin θ ^ 2‖ ^ (-(1 / 2 : ℝ)) := by
  have hnorm : ‖(1 : ℂ)‖ - ‖z * (Real.sin θ : ℂ) ^ 2‖ = 1 - ‖z‖ * Real.sin θ ^ 2 := by
    simp only [norm_one, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h := abs_norm_sub_norm_le (1 : ℂ) (z * (Real.sin θ : ℂ) ^ 2)
  rw [hnorm, ← Real.norm_eq_abs] at h
  have hr := Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hne) h (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  simpa only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    using (Complex.norm_cpow_real (1 - z * (Real.sin θ : ℂ) ^ 2) (-(1 / 2 : ℝ))).trans_le hr

/-- A radial majorant controls every direction of approach, including the branch cut. -/
theorem complexEllipticK_radial_norm_bound {z : ℂ} (hz : z ∈ ellipticDomain) (hn : 1 < ‖z‖) :
    ‖complexEllipticK z‖ ≤
      ‖z‖ ^ (-(1 / 2 : ℝ)) * ellipticK ‖z‖⁻¹ + ellipticK (1 - ‖z‖) := by
  have hi := (complexEllipticK_integrand_continuous hz).intervalIntegrable (μ := volume) 0 (Real.pi / 2)
  unfold complexEllipticK
  calc
    _ ≤ ∫ θ in (0 : ℝ)..Real.pi / 2,
        ‖(1 - z * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by positivity)
    _ ≤ ∫ θ in (0 : ℝ)..Real.pi / 2, ‖1 - ‖z‖ * Real.sin θ ^ 2‖ ^ (-(1 / 2 : ℝ)) := by
      apply intervalIntegral.integral_mono_ae_restrict (by positivity) hi.norm
        (elliptic_cut_majorant_intervalIntegrable hn _ _)
      filter_upwards [ae_restrict_of_ae (elliptic_cut_ae_nonzero hn),
        ae_restrict_mem measurableSet_Icc] with θ hθ hmem
      exact elliptic_radial_integrand_bound z θ (hθ hmem)
    _ = _ := elliptic_cut_majorant_integral hn

theorem complexEllipticK_radial_norm_bound_below {z : ℂ} (hz : z ∈ ellipticDomain) (hn : ‖z‖ < 1) :
    ‖complexEllipticK z‖ ≤ ellipticK ‖z‖ := by
  have hi := (complexEllipticK_integrand_continuous hz).intervalIntegrable (μ := volume) 0 (Real.pi / 2)
  unfold complexEllipticK ellipticK
  calc
    _ ≤ ∫ θ in (0 : ℝ)..Real.pi / 2,
        ‖(1 - z * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by positivity)
    _ ≤ _ := by
      apply intervalIntegral.integral_mono (by positivity) hi.norm (ellipticK_integrable hn)
      intro θ
      have hp := ellipticK_base_pos hn θ
      simpa only [Real.norm_eq_abs, abs_of_pos hp] using elliptic_radial_integrand_bound z θ hp.ne'

theorem complexEllipticK_radial_mild_bound {z : ℂ} (hz : z ∈ ellipticDomain) (hn : ‖z‖ ≠ 1) :
    ‖complexEllipticK z‖ ≤ 8 * |1 - ‖z‖| ^ (-(1 / 16 : ℝ)) + Real.pi / 2 := by
  rcases lt_or_gt_of_ne hn with h | h
  · have hb := (complexEllipticK_radial_norm_bound_below hz h).trans (ellipticK_mild_bound h)
    rw [abs_of_pos (sub_pos.mpr h)]
    linarith [Real.pi_pos]
  · have hb := (complexEllipticK_radial_norm_bound hz h).trans (ellipticK_cut_mild_bound h)
    have ha : |1 - ‖z‖| = ‖z‖ - 1 := by rw [abs_of_neg (by linarith : 1 - ‖z‖ < 0)]; ring
    rwa [ha]

theorem ellipticK_negative_large_bound {m : ℝ} (hm : 0 < m) :
    ellipticK (1 - m) ≤ 8 * m ^ (-(7 / 16 : ℝ)) := by
  rw [ellipticK_parameter_transform (by linarith : 1 - m < 1), sub_sub_cancel]
  have he : (1 - m) / (1 - m - 1) = 1 - m⁻¹ := by
    rw [show 1 - m - 1 = -m by ring]
    field_simp
    ring
  rw [he]
  have h := mul_le_mul_of_nonneg_left (ellipticK_mild_bound (sub_lt_self 1 (inv_pos.mpr hm)))
    (Real.rpow_nonneg hm.le (-(1 / 2 : ℝ)))
  rw [sub_sub_cancel, Real.inv_rpow hm.le, ← Real.rpow_neg hm.le] at h
  have hp : m ^ (-(1 / 2 : ℝ)) * (8 * m ^ (- -(1 / 16 : ℝ))) =
      8 * m ^ (-(7 / 16 : ℝ)) := by
    rw [mul_left_comm, ← Real.rpow_add hm]
    norm_num
  rwa [hp] at h

theorem elliptic_cut_large_bound {m : ℝ} (hm : 2 ≤ m) :
    m ^ (-(1 / 2 : ℝ)) * ellipticK m⁻¹ + ellipticK (1 - m) ≤
      (ellipticK (1 / 2) + 8) * m ^ (-(7 / 16 : ℝ)) := by
  have hm0 : 0 < m := by linarith
  have hi : m⁻¹ ≤ 1 / 2 := by exact (inv_le_comm₀ hm0 (by norm_num)).mpr (by norm_num; exact hm)
  have hk := ellipticK_mono hi (by norm_num : (1 / 2 : ℝ) < 1)
  have hp : m ^ (-(1 / 2 : ℝ)) ≤ m ^ (-(7 / 16 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hmul := mul_le_mul hp hk (ellipticK_pos (by linarith : m⁻¹ < 1)).le
    (Real.rpow_nonneg hm0.le (-(7 / 16 : ℝ)))
  have hn := ellipticK_negative_large_bound hm0
  nlinarith

theorem complexEllipticK_large_bound {z : ℂ} (hz : z ∈ ellipticDomain) (hn : 2 ≤ ‖z‖) :
    ‖complexEllipticK z‖ ≤ (ellipticK (1 / 2) + 8) * ‖z‖ ^ (-(7 / 16 : ℝ)) :=
  (complexEllipticK_radial_norm_bound hz (by linarith)).trans (elliptic_cut_large_bound hn)

end AperyMoments
