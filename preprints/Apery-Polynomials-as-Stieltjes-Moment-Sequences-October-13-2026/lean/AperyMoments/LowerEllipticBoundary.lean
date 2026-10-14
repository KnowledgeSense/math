import AperyMoments.LowerEllipticPositive
import AperyMoments.ArcsineSubstitution

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem lowerElliptic_first_substitution {c θ : ℝ} (hc : 0 < c)
    (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    ((c - (Real.sqrt c * Real.sin θ) ^ 2) ^ (-(1 / 2 : ℝ)) *
      (1 - c * (Real.sqrt c * Real.sin θ) ^ 2) ^ (-(1 / 2 : ℝ))) *
      (Real.sqrt c * Real.cos θ) =
        (1 - c ^ 2 * Real.sin θ ^ 2) ^ (-(1 / 2 : ℝ)) := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hsq := Real.sq_sqrt hc.le
  have hbase : c - (Real.sqrt c * Real.sin θ) ^ 2 =
      (Real.sqrt c * Real.cos θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hbase, inverse_sqrt_rpow (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos (mul_pos hs hcos)]
  have harg : 1 - c * (Real.sqrt c * Real.sin θ) ^ 2 =
      1 - c ^ 2 * Real.sin θ ^ 2 := by rw [mul_pow, hsq]; ring
  rw [harg]
  field_simp


/-- The first interval in the lower-lip continuation has precisely the complementary
elliptic integral as its imaginary coefficient. -/
theorem lowerElliptic_first_interval {c : ℝ} (hc : 0 < c) (_hc1 : c < 1) :
    (∫ t in (0 : ℝ)..Real.sqrt c,
      (c - t ^ 2) ^ (-(1 / 2 : ℝ)) *
        (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ))) = ellipticK (c ^ 2) := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (f := fun θ => Real.sqrt c * Real.sin θ)
    (f' := fun θ => Real.sqrt c * Real.cos θ)
    (g := fun t => (c - t ^ 2) ^ (-(1 / 2 : ℝ)) *
      (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ)))
    (by fun_prop)
    (fun θ _ => (Real.hasDerivAt_sin θ).const_mul _)
    (by
      intro θ hθ
      rw [min_eq_left (by positivity), max_eq_right (by positivity)] at hθ
      exact mul_nonneg hs.le (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).le)
  simp only [Real.sin_zero, mul_zero, Real.sin_pi_div_two, mul_one] at he
  rw [← he, ellipticK]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ θ : ℝ ∂volume, θ ≠ Real.pi / 2 := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using
      (measure_singleton (Real.pi / 2) : volume {Real.pi / 2} = 0)
  filter_upwards [hne] with θ hθne hθ
  rw [uIoc_of_le (by positivity)] at hθ
  exact lowerElliptic_first_substitution hc
    ⟨hθ.1, lt_of_le_of_ne hθ.2 hθne⟩

/-- Endpoint singularities in the first contribution are integrable. -/
theorem lowerElliptic_first_interval_integrable {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    IntervalIntegrable (fun t => (c - t ^ 2) ^ (-(1 / 2 : ℝ)) *
      (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ))) volume 0 (Real.sqrt c) := by
  have hi := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (f := fun θ => Real.sqrt c * Real.sin θ)
    (f' := fun θ => Real.sqrt c * Real.cos θ)
    (g := fun t => (c - t ^ 2) ^ (-(1 / 2 : ℝ)) *
      (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ)))
    (by fun_prop)
    (fun θ _ => (Real.hasDerivAt_sin θ).const_mul _)
    (by
      intro θ hθ
      rw [min_eq_left (by positivity), max_eq_right (by positivity)] at hθ
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).le)
  simp only [Real.sin_zero, mul_zero, Real.sin_pi_div_two, mul_one] at hi
  apply hi.mp
  apply (ellipticK_integrable (show c ^ 2 < 1 by nlinarith)).congr_ae
  have hne : ∀ᵐ θ : ℝ ∂volume, θ ≠ Real.pi / 2 := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using
      (measure_singleton (Real.pi / 2) : volume {Real.pi / 2} = 0)
  apply (ae_restrict_iff' measurableSet_uIoc).mpr
  filter_upwards [hne] with θ hθne hθ
  rw [uIoc_of_le (by positivity)] at hθ
  exact (lowerElliptic_first_substitution hc
    ⟨hθ.1, lt_of_le_of_ne hθ.2 hθne⟩).symm

end AperyMoments
