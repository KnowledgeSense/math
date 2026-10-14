import AperyMoments.LowerEllipticMiddle

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem elliptic_inversion_image {a : ℝ} (ha : 0 < a) :
    (fun t : ℝ => t⁻¹) '' Ioi a⁻¹ = Ioo 0 a := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu0 : 0 < u := (inv_pos.2 ha).trans hu
    exact ⟨inv_pos.2 hu0, (inv_lt_comm₀ hu0 ha).2 hu⟩
  · intro ht
    refine ⟨t⁻¹, ?_, inv_inv t⟩
    exact (inv_lt_inv₀ ha ht.1).2 ht.2

theorem elliptic_inversion_identity {c t : ℝ} (ht : 0 < t)
    (hA : 0 < c * t ^ 2 - 1) (hB : 0 < t ^ 2 - c) :
    |-(t ^ 2)⁻¹| *
      ((c - (t⁻¹) ^ 2) ^ (-(1 / 2 : ℝ)) *
        (1 - c * (t⁻¹) ^ 2) ^ (-(1 / 2 : ℝ))) =
      (t ^ 2 - c) ^ (-(1 / 2 : ℝ)) *
        (c * t ^ 2 - 1) ^ (-(1 / 2 : ℝ)) := by
  have heA : c - (t⁻¹) ^ 2 = (c * t ^ 2 - 1) / t ^ 2 := by field_simp
  have heB : 1 - c * (t⁻¹) ^ 2 = (t ^ 2 - c) / t ^ 2 := by field_simp
  rw [heA, heB, inverse_sqrt_rpow (by positivity), inverse_sqrt_rpow (by positivity),
    inverse_sqrt_rpow hB.le, inverse_sqrt_rpow hA.le,
    Real.sqrt_div hA.le, Real.sqrt_div hB.le, Real.sqrt_sq ht.le,
    abs_neg, abs_of_pos (by positivity : 0 < (t ^ 2)⁻¹)]
  field_simp

theorem elliptic_tail_bases_pos {c t : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (ht : (Real.sqrt c)⁻¹ < t) : 0 < c * t ^ 2 - 1 ∧ 0 < t ^ 2 - c := by
  have hs := Real.sqrt_pos.2 hc
  have hs1 : Real.sqrt c < 1 := by
    nlinarith [Real.sq_sqrt hc.le]
  have hst : 1 < Real.sqrt c * t := by
    have := mul_lt_mul_of_pos_left ht hs
    simpa only [mul_inv_cancel₀ hs.ne'] using this
  have ht0 : 0 < t := (inv_pos.2 hs).trans ht
  have hsq := Real.sq_sqrt hc.le
  have hmul : (Real.sqrt c * t) ^ 2 = c * t ^ 2 := by rw [mul_pow, hsq]
  constructor
  · nlinarith [sq_nonneg (Real.sqrt c * t - 1)]
  · have : 1 < t := by nlinarith
    nlinarith

/-- The unbounded third contribution equals the first one by reciprocal substitution. -/
theorem lowerElliptic_tail_interval {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    (∫ t in Ioi (Real.sqrt c)⁻¹,
      (t ^ 2 - c) ^ (-(1 / 2 : ℝ)) *
        (c * t ^ 2 - 1) ^ (-(1 / 2 : ℝ))) = ellipticK (c ^ 2) := by
  have he := integral_image_eq_integral_abs_deriv_smul
    (s := Ioi (Real.sqrt c)⁻¹) (f := fun t : ℝ => t⁻¹)
    (f' := fun t => -(t ^ 2)⁻¹) measurableSet_Ioi
    (fun t ht => (hasDerivAt_inv (ne_of_gt
      ((inv_pos.2 (Real.sqrt_pos.2 hc)).trans ht))).hasDerivWithinAt)
    (fun _ _ _ _ h => inv_injective h)
    (fun t => (c - t ^ 2) ^ (-(1 / 2 : ℝ)) *
      (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ)))
  rw [elliptic_inversion_image (Real.sqrt_pos.2 hc)] at he
  have hcongr : (∫ t in Ioi (Real.sqrt c)⁻¹,
      |-(t ^ 2)⁻¹| • ((c - (t⁻¹) ^ 2) ^ (-(1 / 2 : ℝ)) *
        (1 - c * (t⁻¹) ^ 2) ^ (-(1 / 2 : ℝ)))) =
      ∫ t in Ioi (Real.sqrt c)⁻¹,
        (t ^ 2 - c) ^ (-(1 / 2 : ℝ)) *
          (c * t ^ 2 - 1) ^ (-(1 / 2 : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact elliptic_inversion_identity ((inv_pos.2 (Real.sqrt_pos.2 hc)).trans ht)
      (elliptic_tail_bases_pos hc hc1 ht).1 (elliptic_tail_bases_pos hc hc1 ht).2
  rw [hcongr] at he
  rw [← he, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
    (Real.sqrt_nonneg c)]
  exact lowerElliptic_first_interval hc hc1

theorem lowerElliptic_tail_integrable {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    IntegrableOn (fun t => (t ^ 2 - c) ^ (-(1 / 2 : ℝ)) *
      (c * t ^ 2 - 1) ^ (-(1 / 2 : ℝ))) (Ioi (Real.sqrt c)⁻¹) := by
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioi (Real.sqrt c)⁻¹) (f := fun t : ℝ => t⁻¹)
    (f' := fun t => -(t ^ 2)⁻¹) measurableSet_Ioi
    (fun t ht => (hasDerivAt_inv (ne_of_gt
      ((inv_pos.2 (Real.sqrt_pos.2 hc)).trans ht))).hasDerivWithinAt)
    (fun _ _ _ _ h => inv_injective h)
    (fun t => (c - t ^ 2) ^ (-(1 / 2 : ℝ)) *
      (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ)))
  rw [elliptic_inversion_image (Real.sqrt_pos.2 hc)] at hi
  have hfirst := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (Real.sqrt_nonneg c)).mp (lowerElliptic_first_interval_integrable hc hc1)
  apply (hi.mp hfirst).congr
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  exact Filter.Eventually.of_forall fun t ht =>
    elliptic_inversion_identity ((inv_pos.2 (Real.sqrt_pos.2 hc)).trans ht)
      (elliptic_tail_bases_pos hc hc1 ht).1 (elliptic_tail_bases_pos hc hc1 ht).2

end AperyMoments
