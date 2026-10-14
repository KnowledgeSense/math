import AperyMoments.ProductArcsineFubini

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem positiveArcsine_setIntegral : (∫ t in Ioo (0 : ℝ) 1, positiveArcsineWeight t) = Real.pi / 2 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact positiveArcsine_integral

theorem ellipticComplement_integrable :
    IntegrableOn (fun z : ℝ => ellipticK (1 - z ^ 2)) (Ioo 0 1) := by
  have hi := productArcsine_test_integrable (show Continuous (fun _ : ℝ => (1 : ℂ)) from continuous_const)
    (show ∀ t ∈ Icc (0 : ℝ) 1, ‖(1 : ℂ)‖ ≤ 1 by intros; norm_num)
  have hr := hi.re
  change IntegrableOn (fun z : ℝ => ((1 : ℂ) * (ellipticK (1 - z ^ 2) : ℂ)).re) (Ioo 0 1) at hr
  simpa only [one_mul, Complex.ofReal_re] using hr

theorem ellipticComplement_integral :
    (∫ z in Ioo (0 : ℝ) 1, ellipticK (1 - z ^ 2)) = Real.pi ^ 2 / 4 := by
  have h := productArcsine_test_integral_real (show Continuous (fun _ : ℝ => (1 : ℝ)) from continuous_const)
    (show ∀ t ∈ Icc (0 : ℝ) 1, |(1 : ℝ)| ≤ 1 by intros; norm_num)
  simp only [one_mul, positiveArcsine_integral] at h
  rw [integral_mul_const, positiveArcsine_setIntegral] at h
  linarith

def positiveArcsineMoment (n : ℕ) : ℝ := ∫ t in (0 : ℝ)..1, t ^ n * positiveArcsineWeight t

theorem ellipticComplement_moment (n : ℕ) :
    (∫ z in Ioo (0 : ℝ) 1, z ^ n * ellipticK (1 - z ^ 2)) = positiveArcsineMoment n ^ 2 := by
  have h := productArcsine_test_integral_real (show Continuous (fun z : ℝ => z ^ n) by fun_prop)
    (show ∀ t ∈ Icc (0 : ℝ) 1, |t ^ n| ≤ 1 by
      intro t ht
      rw [abs_of_nonneg (pow_nonneg ht.1 _)]
      exact pow_le_one₀ ht.1 ht.2)
  have hin (r : ℝ) : (∫ t in (0 : ℝ)..1, (r * t) ^ n * positiveArcsineWeight t) = r ^ n * positiveArcsineMoment n := by
    simp only [mul_pow, mul_assoc, intervalIntegral.integral_const_mul, positiveArcsineMoment]
  simp_rw [hin] at h
  have hout : (∫ r in Ioo (0 : ℝ) 1, positiveArcsineWeight r * (r ^ n * positiveArcsineMoment n)) =
      positiveArcsineMoment n * positiveArcsineMoment n := by
    rw [show (fun r : ℝ => positiveArcsineWeight r * (r ^ n * positiveArcsineMoment n)) =
      (fun r => positiveArcsineMoment n * (r ^ n * positiveArcsineWeight r)) by funext r; ring,
      integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rfl
  rw [hout] at h
  simpa only [pow_two] using h

end AperyMoments
