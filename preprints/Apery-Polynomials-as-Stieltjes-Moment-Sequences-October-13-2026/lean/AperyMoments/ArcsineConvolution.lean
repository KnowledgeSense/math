import AperyMoments.LowerEllipticPositive

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem scaled_cos_image {b : ℝ} (hb : 0 < b) :
    (fun θ : ℝ => b * Real.cos θ) '' Ioo 0 Real.pi = Ioo (-b) b := by
  ext u
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    have hlow := Real.strictAntiOn_cos ⟨hθ.1.le, hθ.2.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hθ.2
    have hhigh := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ ⟨hθ.1.le, hθ.2.le⟩ hθ.1
    simp only [Real.cos_pi, Real.cos_zero] at hlow hhigh
    constructor <;> nlinarith
  · intro hu
    have hlow : -1 < u / b := (lt_div_iff₀ hb).2 (by linarith [hu.1])
    have hhigh : u / b < 1 := (div_lt_iff₀ hb).2 (by linarith [hu.2])
    refine ⟨Real.arccos (u / b), ⟨Real.arccos_pos.2 hhigh, Real.arccos_lt_pi.2 hlow⟩, ?_⟩
    dsimp only
    rw [Real.cos_arccos hlow.le hhigh.le]
    field_simp

theorem scaled_cos_sqrt {b θ : ℝ} (hb : 0 < b) (hθ : θ ∈ Ioo 0 Real.pi) :
    Real.sqrt (b ^ 2 - (b * Real.cos θ) ^ 2) = b * Real.sin θ := by
  have he : b ^ 2 - (b * Real.cos θ) ^ 2 = (b * Real.sin θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [he, Real.sqrt_sq (mul_nonneg hb.le (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le)]

/-- Exact change from the arcsine density to the uniform angle measure. -/
theorem arcsine_integral_substitution {b : ℝ} (hb : 0 < b) (F : ℝ → ℂ) :
    (∫ u in Ioo (-b) b, (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ • F u) =
      ∫ θ in (0 : ℝ)..Real.pi, F (b * Real.cos θ) := by
  have he := integral_image_eq_integral_abs_deriv_smul
    (s := Ioo (0 : ℝ) Real.pi) (f := fun θ : ℝ => b * Real.cos θ)
    (f' := fun θ => b * -Real.sin θ) measurableSet_Ioo
    (fun θ _ => ((Real.hasDerivAt_cos θ).const_mul b).hasDerivWithinAt)
    (fun θ hθ φ hφ heq => Real.strictAntiOn_cos.injOn
      ⟨hθ.1.le, hθ.2.le⟩ ⟨hφ.1.le, hφ.2.le⟩ (mul_left_cancel₀ hb.ne' heq))
    (fun u => (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ • F u)
  rw [scaled_cos_image hb] at he
  rw [he, intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ hθ
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  dsimp only
  rw [scaled_cos_sqrt hb hθ, abs_of_neg (mul_neg_of_pos_of_neg hb (neg_neg_of_pos hs)),
    mul_neg, neg_neg, smul_smul, mul_inv_cancel₀ (mul_pos hb hs).ne', one_smul]

theorem arcsine_integrable_iff {b : ℝ} (hb : 0 < b) (F : ℝ → ℂ) :
    IntegrableOn (fun u => (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ • F u) (Ioo (-b) b) ↔
      IntervalIntegrable (fun θ => F (b * Real.cos θ)) volume 0 Real.pi := by
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioo (0 : ℝ) Real.pi) (f := fun θ : ℝ => b * Real.cos θ)
    (f' := fun θ => b * -Real.sin θ) measurableSet_Ioo
    (fun θ _ => ((Real.hasDerivAt_cos θ).const_mul b).hasDerivWithinAt)
    (fun θ hθ φ hφ heq => Real.strictAntiOn_cos.injOn
      ⟨hθ.1.le, hθ.2.le⟩ ⟨hφ.1.le, hφ.2.le⟩ (mul_left_cancel₀ hb.ne' heq))
    (fun u => (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ • F u)
  rw [scaled_cos_image hb] at hi
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le Real.pi_pos.le]
  apply hi.trans
  apply integrableOn_congr_fun _ measurableSet_Ioo
  intro θ hθ
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  dsimp only
  rw [scaled_cos_sqrt hb hθ, abs_of_neg (mul_neg_of_pos_of_neg hb (neg_neg_of_pos hs)),
    mul_neg, neg_neg, smul_smul, mul_inv_cancel₀ (mul_pos hb hs).ne', one_smul]

theorem arcsine_integral_substitution_real {b : ℝ} (hb : 0 < b) (F : ℝ → ℝ) :
    (∫ u in Ioo (-b) b, (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ * F u) =
      ∫ θ in (0 : ℝ)..Real.pi, F (b * Real.cos θ) := by
  have h := arcsine_integral_substitution hb (fun u => (F u : ℂ))
  simp_rw [Complex.real_smul, ← Complex.ofReal_mul] at h
  rw [integral_complex_ofReal, intervalIntegral.integral_ofReal] at h
  exact_mod_cast h

/-- The angular definition is exactly the source's arcsine convolution. -/
theorem angular_convolution_eq_arcsine {b : ℝ} (hb : 0 < b) (F : ℝ → ℂ) (w : ℝ) :
    (Real.pi : ℂ)⁻¹ * (∫ θ in (0 : ℝ)..Real.pi, F (w - b * Real.cos θ)) =
      (Real.pi : ℂ)⁻¹ * (∫ u in Ioo (-b) b,
        (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ • F (w - u)) := by
  rw [arcsine_integral_substitution hb]

end AperyMoments
