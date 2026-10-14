import AperyMoments.CauchyDomain

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem imaginary_mul_cauchy_tendsto_zero {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    (x : ℝ) : Tendsto (fun z : ℂ => (z.im : ℂ) * densityCauchyTransform h z)
      (𝓝[{z : ℂ | z.im ≠ 0}] (x : ℂ)) (𝓝 0) := by
  have he (z : ℂ) : (z.im : ℂ) * densityCauchyTransform h z =
      ∫ t : ℝ, (z.im : ℂ) * densityCauchyKernel h z t := by
    rw [densityCauchyTransform, integral_const_mul]
  simp_rw [he]
  have hz : (0 : ℂ) = ∫ _t : ℝ, (0 : ℂ) := by simp
  rw [hz]
  apply tendsto_integral_filter_of_dominated_convergence (fun t => |h t|)
  · apply Eventually.of_forall
    intro z
    exact (aestronglyMeasurable_const.mul (densityCauchyKernel_measurable hh z).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    apply Eventually.of_forall
    intro t
    have hd : 0 < ‖z - (t : ℂ)‖ := by
      have hb := cauchy_separation_nonreal hz t
      exact (abs_pos.mpr hz).trans_le hb
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, densityCauchyKernel, norm_div,
      Complex.norm_real, Real.norm_eq_abs]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (cauchy_separation_nonreal hz t) (abs_nonneg (h t))
  · exact hi.abs
  · have hne : ∀ᵐ t : ℝ ∂volume, t ≠ x := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton x : volume {x} = 0)
    filter_upwards [hne] with t ht
    have hd : (x : ℂ) - t ≠ 0 := by
      rw [← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr ht.symm)
    have hc : ContinuousAt (fun z : ℂ => (z.im : ℂ) * densityCauchyKernel h z t) (x : ℂ) := by
      unfold densityCauchyKernel
      exact (by fun_prop : ContinuousAt (fun z : ℂ => (z.im : ℂ)) (x : ℂ)).mul
        (continuousAt_const.div (by fun_prop) hd)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

end AperyMoments
