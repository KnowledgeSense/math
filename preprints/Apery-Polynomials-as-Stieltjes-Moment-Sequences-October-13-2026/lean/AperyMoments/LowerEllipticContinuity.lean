import AperyMoments.LowerEllipticScaled

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem negative_real_parameter_tendsto (c : ℝ) :
    Tendsto (fun z : ℂ => -z.re) (𝓝[{z : ℂ | z.im < 0}] (-(c : ℂ))) (𝓝 c) := by
  convert Complex.continuous_re.neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
  simp

theorem negative_real_endpoint_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun z : ℂ => (Real.sqrt (-z.re))⁻¹)
      (𝓝[{z : ℂ | z.im < 0}] (-(c : ℂ))) (𝓝 (Real.sqrt c)⁻¹) :=
  ((Real.continuous_sqrt.tendsto c).comp (negative_real_parameter_tendsto c)).inv₀
    (Real.sqrt_pos.2 hc).ne'

theorem scaledEllipticKernel_negative_tendsto {c s : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hs : 0 ≤ s) (hcut : s < (Real.sqrt c)⁻¹) (hne : s ^ 2 - 1 ≠ 0) :
    Tendsto (fun z : ℂ => scaledEllipticKernel (-z.re) z s)
      (𝓝[{z : ℂ | z.im < 0}] (-(c : ℂ)))
      (𝓝 (starRingEnd ℂ (scaledEllipticKernel c (-c) s))) := by
  let l := 𝓝[{z : ℂ | z.im < 0}] (-(c : ℂ))
  have hcpos : ∀ᶠ z : ℂ in l, 0 < -z.re :=
    (negative_real_parameter_tendsto c).eventually (Ioi_mem_nhds hc)
  have heps : Tendsto (fun z : ℂ => -z.im / (-z.re)) l (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have him : Tendsto (fun z : ℂ => -z.im) l (𝓝 (0 : ℝ)) := by
        convert Complex.continuous_im.neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
        simp
      have hd := him.div (negative_real_parameter_tendsto c) hc.ne'
      rw [zero_div] at hd
      exact hd
    · filter_upwards [hcpos, self_mem_nhdsWithin] with z hz hzim
      exact div_pos (neg_pos.2 hzim) hz
  have hfirst := (inverse_sqrt_lower_affine_limit hne (by norm_num : (0 : ℝ) < 1)).comp heps
  have hst : Real.sqrt c * s < 1 := by
    have h := mul_lt_mul_of_pos_left hcut (Real.sqrt_pos.2 hc)
    simpa only [mul_inv_cancel₀ (Real.sqrt_pos.2 hc).ne'] using h
  have hs2 : c * s ^ 2 < 1 := by
    have hh : (Real.sqrt c * s) ^ 2 = c * s ^ 2 := by rw [mul_pow, Real.sq_sqrt hc.le]
    nlinarith [mul_nonneg (Real.sqrt_nonneg c) hs]
  have hB : 0 < 1 - c ^ 2 * s ^ 2 := by nlinarith
  have hbase : Tendsto (fun z : ℂ => 1 + z * (((-z.re) * s ^ 2 : ℝ) : ℂ)) l
      (𝓝 ((1 - c ^ 2 * s ^ 2 : ℝ) : ℂ)) := by
    convert (show Continuous (fun z : ℂ => 1 + z * (((-z.re) * s ^ 2 : ℝ) : ℂ)) by
      fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp
    ring
  have hsecond := (continuousAt_cpow_const (b := (-(1 / 2 : ℂ)))
    (a := ((1 - c ^ 2 * s ^ 2 : ℝ) : ℂ))
    (Complex.mem_slitPlane_iff.mpr (Or.inl hB))).tendsto.comp hbase
  have hprod := hfirst.mul hsecond
  have hvalue : starRingEnd ℂ (scaledEllipticKernel c (-c) s) =
      starRingEnd ℂ (((s ^ 2 - 1 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) *
        ((1 - c ^ 2 * s ^ 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) := by
    rw [scaledEllipticKernel_eq hc (-c) (by simp), map_mul]
    simp only [Complex.neg_im, Complex.ofReal_im, neg_zero, zero_div, Complex.ofReal_zero,
      mul_zero, add_zero]
    congr 1
    rw [show 1 + -(c : ℂ) * ((c * s ^ 2 : ℝ) : ℂ) =
      ((1 - c ^ 2 * s ^ 2 : ℝ) : ℂ) by push_cast; ring,
      inverse_sqrt_cpow_of_nonneg hB.le, Complex.conj_ofReal]
  rw [hvalue]
  apply hprod.congr'
  filter_upwards [hcpos] with z hz
  rw [scaledEllipticKernel_eq hz z (by simp)]
  dsimp only [Function.comp_apply]
  congr 2
  push_cast
  ring

theorem cutoffEllipticKernel_negative_tendsto {c s : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hs : 0 ≤ s) (hne : s ^ 2 - 1 ≠ 0) (hend : s ≠ (Real.sqrt c)⁻¹) :
    Tendsto (fun z : ℂ => cutoffEllipticKernel (-z.re) z s)
      (𝓝[{z : ℂ | z.im < 0}] (-(c : ℂ)))
      (𝓝 (starRingEnd ℂ (cutoffEllipticKernel c (-c) s))) := by
  rcases lt_or_gt_of_ne hend with hcut | hcut
  · have hevent := (negative_real_endpoint_tendsto hc).eventually (Ioi_mem_nhds hcut)
    rw [cutoffEllipticKernel, Set.indicator_of_mem
      (show s ∈ Iic (Real.sqrt c)⁻¹ from hcut.le)]
    apply (scaledEllipticKernel_negative_tendsto hc hc1 hs hcut hne).congr'
    filter_upwards [hevent] with z hz
    exact (Set.indicator_of_mem (show s ∈ Iic (Real.sqrt (-z.re))⁻¹ from hz.le) _).symm
  · have hevent := (negative_real_endpoint_tendsto hc).eventually (Iio_mem_nhds hcut)
    rw [cutoffEllipticKernel, Set.indicator_of_notMem
      (show s ∉ Iic (Real.sqrt c)⁻¹ from not_le_of_gt hcut), map_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with z hz
    exact (Set.indicator_of_notMem (show s ∉ Iic (Real.sqrt (-z.re))⁻¹ from not_le_of_gt hz) _).symm

/-- Unrestricted lower-half-plane convergence, with the branch singularity fixed by scaling. -/
theorem lowerEllipticIntegral_negative_boundary {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Tendsto lowerEllipticIntegral (𝓝[{z : ℂ | z.im < 0}] (-(c : ℂ)))
      (𝓝 ((ellipticK (1 - c ^ 2) : ℂ) + 2 * Complex.I * (ellipticK (c ^ 2) : ℂ))) := by
  let δ := (1 - c) / 2
  let L := (Real.sqrt c)⁻¹ + 1
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hcδ : c < 1 - δ := by dsimp [δ]; linarith
  have hend : (Real.sqrt c)⁻¹ < L := by dsimp [L]; linarith
  let l := 𝓝[{z : ℂ | z.im < 0}] (-(c : ℂ))
  have hnear : ∀ᶠ z : ℂ in l, 0 < -z.re ∧ -z.re ≤ 1 - δ ∧
      (Real.sqrt (-z.re))⁻¹ ≤ L ∧ z.im < 0 := by
    filter_upwards [(negative_real_parameter_tendsto c).eventually (Ioi_mem_nhds hc),
      (negative_real_parameter_tendsto c).eventually (Iio_mem_nhds hcδ),
      (negative_real_endpoint_tendsto hc).eventually (Iio_mem_nhds hend),
      self_mem_nhdsWithin] with z hz1 hz2 hz3 hz4
    exact ⟨hz1, hz2.le, hz3.le, hz4⟩
  have hne (a : ℝ) : ∀ᵐ s : ℝ ∂volume, s ≠ a := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton a : volume {a} = 0)
  have hi : IntervalIntegrable (fun s : ℝ =>
      δ ^ (-(1 / 2 : ℝ)) * ‖s ^ 2 - 1‖ ^ (-(1 / 2 : ℝ))) volume 0 L := by
    have hm := quadratic_inverse_sqrt_locallyIntegrable.integrableOn_isCompact
      (k := Icc (0 : ℝ) L) isCompact_Icc
    apply IntervalIntegrable.const_mul
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hL).mpr hm
  have ht : Tendsto (fun z : ℂ => ∫ s in (0 : ℝ)..L, cutoffEllipticKernel (-z.re) z s) l
      (𝓝 (∫ s in (0 : ℝ)..L, starRingEnd ℂ (cutoffEllipticKernel c (-c) s))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun s : ℝ => δ ^ (-(1 / 2 : ℝ)) * ‖s ^ 2 - 1‖ ^ (-(1 / 2 : ℝ)))
    · filter_upwards [hnear] with z hz
      have hcont : Continuous (scaledEllipticKernel (-z.re) z) := by
        unfold scaledEllipticKernel
        exact (show Continuous (fun _ : ℝ => Real.sqrt (-z.re)) from continuous_const).smul ((lowerEllipticKernel_continuous hz.2.2.2).comp
          (show Continuous (fun s : ℝ => Real.sqrt (-z.re) * s) by fun_prop))
      exact hcont.aestronglyMeasurable.indicator measurableSet_Iic
    · filter_upwards [hnear] with z hz
      filter_upwards [hne 1, hne (-1)] with s hs1 hsm hs
      rw [uIoc_of_le hL] at hs
      apply cutoffEllipticKernel_bound hz.1 hδ hz.2.1 z (by simp) hs.1.le
      intro he
      apply hs1
      nlinarith [hs.1]
    · exact hi
    · filter_upwards [hne 1, hne (-1), hne (Real.sqrt c)⁻¹] with s hs1 hsm hsend hs
      rw [uIoc_of_le hL] at hs
      apply cutoffEllipticKernel_negative_tendsto hc hc1 hs.1.le _ hsend
      intro he
      apply hs1
      nlinarith [hs.1]
  have hlimit : (∫ s in (0 : ℝ)..L, starRingEnd ℂ (cutoffEllipticKernel c (-c) s)) =
      starRingEnd ℂ (∫ t in (0 : ℝ)..1, lowerEllipticKernel (-c) t) := by
    rw [intervalIntegral.integral_of_le hL, integral_conj,
      ← intervalIntegral.integral_of_le hL, cutoffEllipticKernel_integral hc hend.le]
  rw [hlimit] at ht
  have htwolim := ht.const_mul (2 : ℂ)
  have htarget : 2 * starRingEnd ℂ (∫ t in (0 : ℝ)..1, lowerEllipticKernel (-c) t) =
      (ellipticK (1 - c ^ 2) : ℂ) + 2 * Complex.I * (ellipticK (c ^ 2) : ℂ) := by
    have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by apply Complex.ext <;> norm_num
    rw [← htwo, ← map_mul, ← lowerEllipticIntegral_half_of_integrable
      (lowerElliptic_negative_integrable hc hc1), lowerEllipticIntegral_negative_value hc hc1]
    simp [htwo]
  rw [htarget] at htwolim
  apply htwolim.congr'
  filter_upwards [hnear] with z hz
  rw [cutoffEllipticKernel_integral hz.1 hz.2.2.1,
    lowerEllipticIntegral_half hz.2.2.2]

end AperyMoments
