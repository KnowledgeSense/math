import AperyMoments.LowerEllipticNegative

set_option maxHeartbeats 800000

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem inverse_sqrt_lower_affine_limit {a b : ℝ} (ha : a ≠ 0) (hb : 0 < b) :
    Tendsto (fun ε : ℝ => ((a : ℂ) - Complex.I * ε * b) ^ (-(1 / 2 : ℂ)))
      (𝓝[>] 0) (𝓝 (starRingEnd ℂ ((a : ℂ) ^ (-(1 / 2 : ℂ))))) := by
  have ht : Tendsto (fun ε : ℝ => (a : ℂ) + Complex.I * ε * b)
      (𝓝[>] 0) (𝓝[{z : ℂ | 0 ≤ z.im}] (a : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · convert (show Continuous (fun ε : ℝ => (a : ℂ) + Complex.I * ε * b) by
        fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
      simp
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < ε at hε
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        zero_mul, one_mul, mul_zero, zero_add, sub_zero]
      positivity
  have hp := (cpow_continuousWithinAt_upper_real ha (-(1 / 2 : ℂ))).tendsto.comp ht
  have hconj := Complex.continuous_conj.continuousAt.tendsto.comp hp
  apply hconj.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hz : (a : ℂ) + Complex.I * ε * b ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa using (mul_pos hε hb).ne'
  have he := Complex.conj_cpow ((a : ℂ) + Complex.I * ε * b) (-(1 / 2 : ℂ))
    (Complex.slitPlane_arg_ne_pi hz)
  have hreal : starRingEnd ℂ (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) := by
    apply Complex.ext <;> norm_num
  rw [hreal] at he
  simpa [sub_eq_add_neg] using he.symm

theorem inverse_sqrt_vertical_bound {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    ‖((a : ℂ) - Complex.I * y) ^ (-(1 / 2 : ℂ))‖ ≤
      ‖(a : ℂ) ^ (-(1 / 2 : ℂ))‖ := by
  have h1 := Complex.norm_cpow_real ((a : ℂ) - Complex.I * y) (-(1 / 2 : ℝ))
  have h2 := Complex.norm_cpow_real (a : ℂ) (-(1 / 2 : ℝ))
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h1 h2
  rw [h1, h2, Complex.norm_real]
  apply Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr ha) _ (by norm_num)
  simpa using Complex.abs_re_le_norm ((a : ℂ) - Complex.I * y)

theorem lowerEllipticKernel_negative_ae_nonzero {c : ℝ} (hc : 0 < c) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ^ 2 - c ≠ 0 ∧ 1 - c * t ^ 2 ≠ 0 := by
  have hne (a : ℝ) : ∀ᵐ t : ℝ ∂volume, t ≠ a := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton a : volume {a} = 0)
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards [hne (Real.sqrt c), hne (Real.sqrt c)⁻¹] with t hta htb ht
  have ht0 : 0 < t := ht
  have hs := Real.sqrt_pos.2 hc
  have hsq := Real.sq_sqrt hc.le
  constructor
  · intro he
    apply hta
    nlinarith
  · intro he
    apply htb
    have hmul : Real.sqrt c * t = 1 := by
      have hh : (Real.sqrt c * t) ^ 2 = c * t ^ 2 := by rw [mul_pow, hsq]
      nlinarith [mul_pos hs ht]
    rw [inv_eq_one_div]
    apply (eq_div_iff hs.ne').2
    linarith

theorem lowerEllipticKernel_negative_vertical_bound (c ε t : ℝ)
    (hA : t ^ 2 - c ≠ 0) (hB : 1 - c * t ^ 2 ≠ 0) :
    ‖lowerEllipticKernel (-(c : ℂ) - Complex.I * ε) t‖ ≤
      ‖lowerEllipticKernel (-c) t‖ := by
  unfold lowerEllipticKernel
  have hAeq : (t : ℂ) ^ 2 + (-(c : ℂ) - Complex.I * ε) =
      ((t ^ 2 - c : ℝ) : ℂ) - Complex.I * ε := by push_cast; ring
  have hBeq : 1 + (-(c : ℂ) - Complex.I * ε) * (t : ℂ) ^ 2 =
      ((1 - c * t ^ 2 : ℝ) : ℂ) - Complex.I * ((ε * t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hA0 : (t : ℂ) ^ 2 + -(c : ℂ) = ((t ^ 2 - c : ℝ) : ℂ) := by push_cast; ring
  have hB0 : 1 + -(c : ℂ) * (t : ℂ) ^ 2 = ((1 - c * t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hAeq, hBeq, hA0, hB0, norm_mul, norm_mul]
  exact mul_le_mul (inverse_sqrt_vertical_bound hA ε)
    (inverse_sqrt_vertical_bound hB (ε * t ^ 2)) (norm_nonneg _) (norm_nonneg _)

theorem lowerEllipticKernel_negative_vertical_limit (c t : ℝ) (ht : 0 < t)
    (hA : t ^ 2 - c ≠ 0) (hB : 1 - c * t ^ 2 ≠ 0) :
    Tendsto (fun ε : ℝ => lowerEllipticKernel (-(c : ℂ) - Complex.I * ε) t)
      (𝓝[>] 0) (𝓝 (starRingEnd ℂ (lowerEllipticKernel (-c) t))) := by
  have h := (inverse_sqrt_lower_affine_limit hA (by norm_num : (0 : ℝ) < 1)).mul
    (inverse_sqrt_lower_affine_limit hB (sq_pos_of_pos ht))
  convert h using 1
  · ext ε
    unfold lowerEllipticKernel
    congr 1
    · congr 1
      push_cast
      ring_nf
    · congr 1
      push_cast
      ring_nf
  · unfold lowerEllipticKernel
    rw [← map_mul]
    congr 1
    congr 1
    congr 1 <;> push_cast <;> ring_nf

/-- The lower continuation has the actual positive imaginary monodromy contribution. -/
theorem lowerEllipticIntegral_negative_lower_limit {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Tendsto (fun ε : ℝ => lowerEllipticIntegral (-(c : ℂ) - Complex.I * ε))
      (𝓝[>] 0) (𝓝 ((ellipticK (1 - c ^ 2) : ℂ) +
        2 * Complex.I * (ellipticK (c ^ 2) : ℂ))) := by
  have hi := lowerElliptic_negative_integrable hc hc1
  have he : (∫ t in Ioi (0 : ℝ), starRingEnd ℂ (lowerEllipticKernel (-c) t)) =
      (ellipticK (1 - c ^ 2) : ℂ) + 2 * Complex.I * (ellipticK (c ^ 2) : ℂ) := by
    change (∫ t in Ioi (0 : ℝ), Complex.conjCLE.toContinuousLinearMap
      (lowerEllipticKernel (-c) t)) = _
    rw [Complex.conjCLE.toContinuousLinearMap.integral_comp_comm hi]
    change starRingEnd ℂ (lowerEllipticIntegral (-c)) = _
    rw [lowerEllipticIntegral_negative_value hc hc1]
    have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by
      apply Complex.ext <;> norm_num
    simp [htwo]
  rw [← he]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖lowerEllipticKernel (-c) t‖)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (lowerEllipticKernel_continuous (by simpa using neg_neg_of_pos (show 0 < ε from hε))).aestronglyMeasurable.restrict
  · apply Filter.Eventually.of_forall
    intro ε
    filter_upwards [lowerEllipticKernel_negative_ae_nonzero hc] with t ht
    exact lowerEllipticKernel_negative_vertical_bound c ε t ht.1 ht.2
  · exact hi.norm
  · filter_upwards [lowerEllipticKernel_negative_ae_nonzero hc,
      ae_restrict_mem measurableSet_Ioi] with t hne ht
    exact lowerEllipticKernel_negative_vertical_limit c t ht hne.1 hne.2

end AperyMoments
