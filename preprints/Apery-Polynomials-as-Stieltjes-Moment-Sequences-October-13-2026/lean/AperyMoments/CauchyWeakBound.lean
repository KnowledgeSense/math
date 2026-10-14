import AperyMoments.CauchyKernelPower
import AperyMoments.SpectralFourthPower

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def spectralFourthIntegral (b : ℝ) : ℝ := ∫ t : ℝ, spectralDensity b t^4

theorem spectralFourthIntegral_nonneg (b : ℝ) : 0 ≤ spectralFourthIntegral b :=
  integral_nonneg (fun _ => by positivity)

theorem spectralCauchyKernel_young_bound (b : ℝ) (z : ℂ) (t : ℝ) :
    ‖densityCauchyKernel (spectralDensity b) z t‖ ≤
      spectralDensity b t^4/4 + ‖z-(t : ℂ)‖^(-(4/3 : ℝ))/(4/3) := by
  have h := Real.young_inequality_of_nonneg (spectralDensity_nonneg b t)
    (inv_nonneg.mpr (norm_nonneg (z-(t : ℂ))))
    (show (4 : ℝ).HolderConjugate (4/3) by rw [Real.holderConjugate_iff]; norm_num)
  have hp : (spectralDensity b t) ^ (4 : ℝ) = spectralDensity b t^4 := by norm_cast
  rw [hp, Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)] at h
  simpa only [densityCauchyKernel, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (spectralDensity_nonneg b t), norm_mul, norm_inv, div_eq_mul_inv] using h

theorem spectralCauchyTransform_weak_bound {b : ℝ} (hb : 0 ≤ b) {z : ℂ}
    (hz : z.im ≠ 0) : ‖spectralCauchyTransform b z‖ ≤
      spectralFourthIntegral b/4 + |z.im|^(-(1/3 : ℝ))*cauchyStudentIntegral/(4/3) := by
  have hi := spectralCauchyKernel_integrable hb (Or.inl hz)
  calc
    ‖spectralCauchyTransform b z‖ ≤ ∫ t : ℝ, ‖densityCauchyKernel (spectralDensity b) z t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (spectralDensity b t^4/4 + ‖z-(t : ℂ)‖^(-(4/3 : ℝ))/(4/3)) :=
      integral_mono hi.norm ((spectralDensity_fourth_integrable b).div_const 4 |>.add
        ((cauchyKernelPower_integrable hz).div_const (4/3))) (spectralCauchyKernel_young_bound b z)
    _ = _ := by
      rw [integral_add ((spectralDensity_fourth_integrable b).div_const 4)
        ((cauchyKernelPower_integrable hz).div_const (4/3))]
      have h₁ : (∫ t : ℝ, spectralDensity b t^4/4) = spectralFourthIntegral b/4 := by
        simp only [div_eq_mul_inv, integral_mul_const, spectralFourthIntegral]
      have h₂ : (∫ t : ℝ, ‖z-(t : ℂ)‖^(-(4/3 : ℝ))/(4/3)) =
          (∫ t : ℝ, ‖z-(t : ℂ)‖^(-(4/3 : ℝ)))/(4/3) := by
        simp only [div_eq_mul_inv, integral_mul_const]
      rw [h₁, h₂, cauchyKernelPower_integral hz]

end AperyMoments
