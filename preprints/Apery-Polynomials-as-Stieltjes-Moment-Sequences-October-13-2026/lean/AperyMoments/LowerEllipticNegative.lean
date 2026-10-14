import AperyMoments.LowerEllipticTail
import AperyMoments.EllipticCutParts

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem inverse_sqrt_cpow_of_nonpos {a : ℝ} (ha : a ≤ 0) :
    (a : ℂ) ^ (-(1 / 2 : ℂ)) = -Complex.I * (((-a) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rcases ha.lt_or_eq with h | rfl
  · exact inverse_sqrt_cpow_of_neg h
  · norm_num [Complex.zero_cpow, Real.zero_rpow]

theorem lowerEllipticKernel_negative_first {c t : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (ht : t ∈ Icc 0 (Real.sqrt c)) :
    lowerEllipticKernel (-c) t = -Complex.I *
      (((c - t ^ 2) ^ (-(1 / 2 : ℝ)) *
        (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hsq := Real.sq_sqrt hc.le
  have ht2 : t ^ 2 ≤ c := by nlinarith [Real.sqrt_nonneg c, ht.1, ht.2]
  have hB : 0 ≤ 1 - c * t ^ 2 := by nlinarith
  unfold lowerEllipticKernel
  rw [show (t : ℂ) ^ 2 + -(c : ℂ) = ((t ^ 2 - c : ℝ) : ℂ) by push_cast; ring,
    show 1 + -(c : ℂ) * (t : ℂ) ^ 2 = ((1 - c * t ^ 2 : ℝ) : ℂ) by push_cast; ring,
    inverse_sqrt_cpow_of_nonpos (by linarith), inverse_sqrt_cpow_of_nonneg hB]
  rw [show -(t ^ 2 - c) = c - t ^ 2 by ring]
  push_cast
  ring

theorem lowerEllipticKernel_negative_middle {c t : ℝ} (hc : 0 < c)
    (ht : t ∈ Icc (Real.sqrt c) (Real.sqrt c)⁻¹) :
    lowerEllipticKernel (-c) t =
      (((t ^ 2 - c) ^ (-(1 / 2 : ℝ)) *
        (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hs := Real.sqrt_pos.2 hc
  have hsq := Real.sq_sqrt hc.le
  have ht0 : 0 ≤ t := hs.le.trans ht.1
  have hA : 0 ≤ t ^ 2 - c := by nlinarith [ht.1]
  have hst : Real.sqrt c * t ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left ht.2 hs.le
    simpa only [mul_inv_cancel₀ hs.ne'] using h
  have hB : 0 ≤ 1 - c * t ^ 2 := by
    have he : (Real.sqrt c * t) ^ 2 = c * t ^ 2 := by rw [mul_pow, hsq]
    nlinarith [mul_nonneg hs.le ht0]
  unfold lowerEllipticKernel
  rw [show (t : ℂ) ^ 2 + -(c : ℂ) = ((t ^ 2 - c : ℝ) : ℂ) by push_cast; ring,
    show 1 + -(c : ℂ) * (t : ℂ) ^ 2 = ((1 - c * t ^ 2 : ℝ) : ℂ) by push_cast; ring,
    inverse_sqrt_cpow_of_nonneg hA, inverse_sqrt_cpow_of_nonneg hB,
    Complex.ofReal_mul]

theorem lowerEllipticKernel_negative_tail {c t : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (ht : (Real.sqrt c)⁻¹ < t) :
    lowerEllipticKernel (-c) t = -Complex.I *
      (((t ^ 2 - c) ^ (-(1 / 2 : ℝ)) *
        (c * t ^ 2 - 1) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have h := elliptic_tail_bases_pos hc hc1 ht
  unfold lowerEllipticKernel
  rw [show (t : ℂ) ^ 2 + -(c : ℂ) = ((t ^ 2 - c : ℝ) : ℂ) by push_cast; ring,
    show 1 + -(c : ℂ) * (t : ℂ) ^ 2 = ((1 - c * t ^ 2 : ℝ) : ℂ) by push_cast; ring,
    inverse_sqrt_cpow_of_nonneg h.2.le, inverse_sqrt_cpow_of_neg (by linarith [h.1])]
  rw [show -(1 - c * t ^ 2) = c * t ^ 2 - 1 by ring]
  push_cast
  ring

theorem lowerElliptic_negative_integrable_parts {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    IntervalIntegrable (lowerEllipticKernel (-c)) volume 0 (Real.sqrt c) ∧
    IntervalIntegrable (lowerEllipticKernel (-c)) volume (Real.sqrt c) (Real.sqrt c)⁻¹ ∧
    IntegrableOn (lowerEllipticKernel (-c)) (Ioi (Real.sqrt c)⁻¹) := by
  have hs := Real.sqrt_pos.2 hc
  have hs1 : Real.sqrt c < 1 := by nlinarith [Real.sq_sqrt hc.le]
  have hab : Real.sqrt c ≤ (Real.sqrt c)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hs).2
    nlinarith
  have hfirst := lowerElliptic_first_interval_integrable hc hc1
  have hmiddle := lowerElliptic_middle_interval_integrable hc hc1
  have htail := lowerElliptic_tail_integrable hc hc1
  constructor
  · apply IntervalIntegrable.congr (fun t ht => ?_)
      (IntervalIntegrable.const_mul (⟨hfirst.1.ofReal, hfirst.2.ofReal⟩ :
        IntervalIntegrable (fun t => (((c - t ^ 2) ^ (-(1 / 2 : ℝ)) *
          (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) volume 0 (Real.sqrt c)) (-Complex.I))
    rw [uIoc_of_le hs.le] at ht
    exact (lowerEllipticKernel_negative_first hc hc1 ⟨ht.1.le, ht.2⟩).symm
  constructor
  · apply IntervalIntegrable.congr (fun t ht => ?_)
      (⟨hmiddle.1.ofReal, hmiddle.2.ofReal⟩ :
        IntervalIntegrable (fun t => (((t ^ 2 - c) ^ (-(1 / 2 : ℝ)) *
          (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) volume
          (Real.sqrt c) (Real.sqrt c)⁻¹)
    rw [uIoc_of_le hab] at ht
    exact (lowerEllipticKernel_negative_middle hc ⟨ht.1.le, ht.2⟩).symm
  · exact IntegrableOn.congr_fun (htail.ofReal.const_mul (-Complex.I))
      (fun t ht => (lowerEllipticKernel_negative_tail hc hc1 ht).symm) measurableSet_Ioi

theorem lowerElliptic_negative_integrable {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    IntegrableOn (lowerEllipticKernel (-c)) (Ioi (0 : ℝ)) := by
  have hi := lowerElliptic_negative_integrable_parts hc hc1
  have hab : 0 ≤ (Real.sqrt c)⁻¹ := by positivity
  have hf := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hi.1.trans hi.2.1)
  rw [← Ioc_union_Ioi_eq_Ioi hab]
  exact hf.union hi.2.2

/-- The direct integral on the principal upper lip has the exact two-term connection value. -/
theorem lowerEllipticIntegral_negative_value {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    lowerEllipticIntegral (-c) = (ellipticK (1 - c ^ 2) : ℂ) -
      2 * Complex.I * (ellipticK (c ^ 2) : ℂ) := by
  have hs := Real.sqrt_pos.2 hc
  have hs1 : Real.sqrt c < 1 := by nlinarith [Real.sq_sqrt hc.le]
  have hab : Real.sqrt c ≤ (Real.sqrt c)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hs).2
    nlinarith
  have hi := lowerElliptic_negative_integrable_parts hc hc1
  have hfirst : (∫ t in (0 : ℝ)..Real.sqrt c, lowerEllipticKernel (-c) t) =
      -Complex.I * (ellipticK (c ^ 2) : ℂ) := by
    calc
      _ = ∫ t in (0 : ℝ)..Real.sqrt c, -Complex.I *
        (((c - t ^ 2) ^ (-(1 / 2 : ℝ)) *
          (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hs.le] at ht
        exact lowerEllipticKernel_negative_first hc hc1 ht
      _ = _ := by rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
        lowerElliptic_first_interval hc hc1]
  have hmiddle : (∫ t in Real.sqrt c..(Real.sqrt c)⁻¹, lowerEllipticKernel (-c) t) =
      (ellipticK (1 - c ^ 2) : ℂ) := by
    calc
      _ = ∫ t in Real.sqrt c..(Real.sqrt c)⁻¹,
        (((t ^ 2 - c) ^ (-(1 / 2 : ℝ)) *
          (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        exact lowerEllipticKernel_negative_middle hc ht
      _ = _ := by rw [intervalIntegral.integral_ofReal, lowerElliptic_middle_interval hc hc1]
  have htail : (∫ t in Ioi (Real.sqrt c)⁻¹, lowerEllipticKernel (-c) t) =
      -Complex.I * (ellipticK (c ^ 2) : ℂ) := by
    calc
      _ = ∫ t in Ioi (Real.sqrt c)⁻¹, -Complex.I *
        (((t ^ 2 - c) ^ (-(1 / 2 : ℝ)) *
          (c * t ^ 2 - 1) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) :=
        setIntegral_congr_fun measurableSet_Ioi fun t ht => lowerEllipticKernel_negative_tail hc hc1 ht
      _ = _ := by rw [integral_const_mul, integral_complex_ofReal, lowerElliptic_tail_interval hc hc1]
  unfold lowerEllipticIntegral
  rw [← intervalIntegral.integral_interval_add_Ioi' (hi.1.trans hi.2.1) hi.2.2,
    ← intervalIntegral.integral_add_adjacent_intervals hi.1 hi.2.1,
    hfirst, hmiddle, htail]
  ring

end AperyMoments
