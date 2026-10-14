import AperyMoments.LowerEllipticInversion

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def scaledEllipticKernel (c : ℝ) (z : ℂ) (s : ℝ) : ℂ :=
  Real.sqrt c • lowerEllipticKernel z (Real.sqrt c * s)

def cutoffEllipticKernel (c : ℝ) (z : ℂ) (s : ℝ) : ℂ :=
  (Iic (Real.sqrt c)⁻¹).indicator (scaledEllipticKernel c z) s

theorem scaledEllipticKernel_eq {c : ℝ} (hc : 0 < c) (z : ℂ)
    (hz : z.re = -c) (s : ℝ) :
    scaledEllipticKernel c z s =
      (((s ^ 2 - 1 : ℝ) : ℂ) + Complex.I * (z.im / c : ℝ)) ^ (-(1 / 2 : ℂ)) *
        (1 + z * ((c * s ^ 2 : ℝ) : ℂ)) ^ (-(1 / 2 : ℂ)) := by
  have hsq := Real.sq_sqrt hc.le
  have hs := Real.sqrt_pos.2 hc
  have hA : ((Real.sqrt c * s : ℝ) : ℂ) ^ 2 + z =
      (c : ℂ) * (((s ^ 2 - 1 : ℝ) : ℂ) + Complex.I * (z.im / c : ℝ)) := by
    have hzc : z = -(c : ℂ) + Complex.I * (z.im : ℂ) := by
      apply Complex.ext <;> simp [hz]
    rw [← Complex.ofReal_pow, mul_pow, hsq]
    conv_lhs => rw [hzc]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hc.ne']
    ring
  have hB : 1 + z * ((Real.sqrt c * s : ℝ) : ℂ) ^ 2 =
      1 + z * ((c * s ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, mul_pow, hsq]
  unfold scaledEllipticKernel lowerEllipticKernel
  rw [hA, hB, inverse_sqrt_cpow_pos_mul hc, inverse_sqrt_rpow hc.le, Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hs.ne']

/-- Moving the branch point by a real scaling preserves the actual bounded integral. -/
theorem cutoffEllipticKernel_integral {c L : ℝ} (hc : 0 < c)
    (hL : (Real.sqrt c)⁻¹ ≤ L) (z : ℂ) :
    (∫ s in (0 : ℝ)..L, cutoffEllipticKernel c z s) =
      ∫ t in (0 : ℝ)..1, lowerEllipticKernel z t := by
  unfold cutoffEllipticKernel
  have he : (∫ s in (0 : ℝ)..L, (Iic (Real.sqrt c)⁻¹).indicator
      (scaledEllipticKernel c z) s) = ∫ s in (0 : ℝ)..(Real.sqrt c)⁻¹,
        scaledEllipticKernel c z s := intervalIntegral.integral_indicator ⟨by positivity, hL⟩
  rw [he]
  unfold scaledEllipticKernel
  rw [intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_left]
  simp [(Real.sqrt_pos.2 hc).ne']

theorem quadratic_inverse_sqrt_locallyIntegrable :
    LocallyIntegrable (fun s : ℝ => ‖s ^ 2 - 1‖ ^ (-(1 / 2 : ℝ))) volume := by
  intro s
  let f : ℝ → ℝ := fun t => t ^ 2 - 1
  have hf : Continuous f := by fun_prop
  by_cases hz : f s = 0
  · apply simple_zero_inverse_sqrt_integrableAt hf.measurable
      (((hasDerivAt_id s).pow 2).sub_const 1) _ hz
    dsimp [f] at hz
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq]
    intro h
    nlinarith
  · have ho : IsOpen {t | f t ≠ 0} := isOpen_ne_fun hf continuous_const
    have hcont : ContinuousOn (fun t => ‖f t‖ ^ (-(1 / 2 : ℝ))) {t | f t ≠ 0} :=
      hf.norm.continuousOn.rpow_const (fun t ht => Or.inl (norm_ne_zero_iff.mpr ht))
    have hi := hcont.integrableAt_nhdsWithin (μ := volume) ho.measurableSet hz
    rwa [nhdsWithin_eq_nhds.mpr (ho.mem_nhds hz)] at hi

theorem inverse_sqrt_cpow_bound_re {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : δ ≤ z.re) :
    ‖z ^ (-(1 / 2 : ℂ))‖ ≤ δ ^ (-(1 / 2 : ℝ)) := by
  have hn := Complex.norm_cpow_real z (-(1 / 2 : ℝ))
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hn
  rw [hn]
  exact Real.rpow_le_rpow_of_nonpos hδ
    (hz.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))) (by norm_num)

/-- Rescaling fixes the square-root singularity and gives a parameter-independent majorant. -/
theorem cutoffEllipticKernel_bound {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hcδ : c ≤ 1 - δ) (z : ℂ) (hz : z.re = -c) {s : ℝ}
    (hs : 0 ≤ s) (hne : s ^ 2 - 1 ≠ 0) :
    ‖cutoffEllipticKernel c z s‖ ≤
      δ ^ (-(1 / 2 : ℝ)) * ‖s ^ 2 - 1‖ ^ (-(1 / 2 : ℝ)) := by
  by_cases hcut : s ≤ (Real.sqrt c)⁻¹
  · rw [cutoffEllipticKernel, Set.indicator_of_mem (show s ∈ Iic (Real.sqrt c)⁻¹ from hcut), scaledEllipticKernel_eq hc z hz,
      norm_mul]
    have hfirst : ‖(((s ^ 2 - 1 : ℝ) : ℂ) + Complex.I * (z.im / c : ℝ)) ^ (-(1 / 2 : ℂ))‖ ≤
        ‖s ^ 2 - 1‖ ^ (-(1 / 2 : ℝ)) := by
      have hb := inverse_sqrt_vertical_bound hne (-(z.im / c))
      have hn := Complex.norm_cpow_real ((s ^ 2 - 1 : ℝ) : ℂ) (-(1 / 2 : ℝ))
      simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hn
      rw [hn, Complex.norm_real] at hb
      simpa only [Complex.ofReal_neg, mul_neg, sub_neg_eq_add] using hb
    have hst : Real.sqrt c * s ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hcut (Real.sqrt_nonneg c)
      simpa only [mul_inv_cancel₀ (Real.sqrt_pos.2 hc).ne'] using h
    have hs2 : c * s ^ 2 ≤ 1 := by
      have hh : (Real.sqrt c * s) ^ 2 = c * s ^ 2 := by rw [mul_pow, Real.sq_sqrt hc.le]
      nlinarith [mul_nonneg (Real.sqrt_nonneg c) hs]
    have hsecond : δ ≤ (1 + z * ((c * s ^ 2 : ℝ) : ℂ)).re := by
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero, hz]
      nlinarith
    calc
      _ ≤ ‖s ^ 2 - 1‖ ^ (-(1 / 2 : ℝ)) * δ ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul hfirst (inverse_sqrt_cpow_bound_re hδ hsecond) (norm_nonneg _)
          (Real.rpow_nonneg (norm_nonneg _) _)
      _ = _ := mul_comm _ _
  · rw [cutoffEllipticKernel, Set.indicator_of_notMem (show s ∉ Iic (Real.sqrt c)⁻¹ from hcut), norm_zero]
    positivity

end AperyMoments
