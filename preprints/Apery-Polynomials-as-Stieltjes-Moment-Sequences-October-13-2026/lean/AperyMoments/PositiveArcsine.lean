import AperyMoments.ProductArcsineSubstitution

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

def positiveArcsineWeight (t : ℝ) : ℝ := (1 - t ^ 2) ^ (-(1 / 2 : ℝ))

theorem positiveArcsine_jacobian {θ : ℝ} (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    positiveArcsineWeight (Real.sin θ) * Real.cos θ = 1 := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  unfold positiveArcsineWeight
  rw [show 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ],
    inverse_sqrt_rpow (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos hc, inv_mul_cancel₀ hc.ne']

theorem positiveArcsine_integrable : IntervalIntegrable positiveArcsineWeight volume 0 1 := by
  have h := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 2) (f := Real.sin) (f' := Real.cos) (g := positiveArcsineWeight)
    Real.continuous_sin.continuousOn (fun θ _ => Real.hasDerivAt_sin θ)
    (fun θ hθ => (Real.cos_pos_of_mem_Ioo ⟨by
      rw [min_eq_left (by positivity)] at hθ
      linarith [hθ.1, Real.pi_pos], by simpa only [max_eq_right (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ.2⟩).le)
  simp only [Real.sin_zero, Real.sin_pi_div_two] at h
  apply h.mp
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by positivity)]
  apply (integrableOn_congr_fun (fun θ hθ => positiveArcsine_jacobian hθ) measurableSet_Ioo).mpr
  exact (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).integrableOn_Icc.mono_set Ioo_subset_Icc_self

theorem positiveArcsine_integral : (∫ t in (0 : ℝ)..1, positiveArcsineWeight t) = Real.pi / 2 := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 2) (f := Real.sin) (f' := Real.cos) (g := positiveArcsineWeight)
    Real.continuous_sin.continuousOn (fun θ _ => Real.hasDerivAt_sin θ)
    (fun θ hθ => (Real.cos_pos_of_mem_Ioo ⟨by
      rw [min_eq_left (by positivity)] at hθ
      linarith [hθ.1, Real.pi_pos], by simpa only [max_eq_right (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ.2⟩).le)
  simp only [Real.sin_zero, Real.sin_pi_div_two] at h
  rw [← h]
  calc
    _ = ∫ _θ in (0 : ℝ)..Real.pi / 2, (1 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      have hne : ∀ᵐ θ : ℝ ∂volume, θ ≠ Real.pi / 2 := by
        apply ae_iff.mpr
        simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton (Real.pi / 2) : volume {Real.pi / 2} = 0)
      filter_upwards [hne] with θ hne hθ
      rw [uIoc_of_le (by positivity)] at hθ
      exact positiveArcsine_jacobian ⟨hθ.1, lt_of_le_of_ne hθ.2 hne⟩
    _ = _ := by simp

theorem positiveArcsineWeight_nonneg {t : ℝ} (ht : t ∈ Icc 0 1) : 0 ≤ positiveArcsineWeight t :=
  Real.rpow_nonneg (by nlinarith [ht.1, ht.2]) _

end AperyMoments
