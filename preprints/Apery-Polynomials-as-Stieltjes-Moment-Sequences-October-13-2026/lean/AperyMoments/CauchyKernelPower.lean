import AperyMoments.CauchyPoisson
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def cauchyStudentKernel (u : ℝ) : ℝ := (1+u^2) ^ (-(2/3 : ℝ))
def cauchyStudentIntegral : ℝ := ∫ u : ℝ, cauchyStudentKernel u

theorem cauchyStudentKernel_integrable : Integrable cauchyStudentKernel := by
  have hi := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
    (r := 4/3) (by norm_num)
  unfold cauchyStudentKernel
  simpa only [Real.norm_eq_abs, sq_abs, show -(4/3 : ℝ)/2 = -(2/3 : ℝ) by norm_num] using hi

theorem cauchyStudentIntegral_nonneg : 0 ≤ cauchyStudentIntegral :=
  integral_nonneg (fun u => Real.rpow_nonneg (by positivity : 0 ≤ 1+u^2) _)

theorem cauchyKernelPower_scaled {z : ℂ} (hz : z.im ≠ 0) (u : ℝ) :
    ‖z-(z.re+|z.im| * u : ℝ)‖ ^ (-(4/3 : ℝ)) =
      |z.im| ^ (-(4/3 : ℝ)) * cauchyStudentKernel u := by
  have hδ : 0 < |z.im| := abs_pos.mpr hz
  have hsq : ‖z-(z.re+|z.im| * u : ℝ)‖^2 = |z.im|^2*(1+u^2) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    nlinarith [sq_abs z.im]
  have hn : ‖z-(z.re+|z.im| * u : ℝ)‖ = |z.im| * Real.sqrt (1+u^2) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hδ.le (Real.sqrt_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt (by positivity), hsq]
  rw [hn, Real.mul_rpow hδ.le (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by positivity : 0 ≤ 1+u^2)]
  unfold cauchyStudentKernel
  norm_num

theorem cauchyKernelPower_integrable {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun t : ℝ => ‖z-(t : ℂ)‖ ^ (-(4/3 : ℝ))) := by
  have hδ : |z.im| ≠ 0 := ne_of_gt (abs_pos.mpr hz)
  have hi := (measurePreserving_sub_right volume z.re).integrable_comp_of_integrable
    (cauchyStudentKernel_integrable.comp_div hδ)
  apply (hi.const_mul (|z.im| ^ (-(4/3 : ℝ)))).congr
  apply Filter.Eventually.of_forall
  intro t
  have he := cauchyKernelPower_scaled hz ((t-z.re)/|z.im|)
  have ha : z.re+|z.im| * ((t-z.re)/|z.im|) = t := by field_simp; ring
  rw [ha] at he
  exact he.symm

theorem cauchyKernelPower_integral {z : ℂ} (hz : z.im ≠ 0) :
    (∫ t : ℝ, ‖z-(t : ℂ)‖ ^ (-(4/3 : ℝ))) =
      |z.im| ^ (-(1/3 : ℝ)) * cauchyStudentIntegral := by
  have hδ := abs_pos.mpr hz
  rw [← affine_integral_pos (fun t : ℝ => ‖z-(t : ℂ)‖ ^ (-(4/3 : ℝ))) z.re hδ]
  simp_rw [cauchyKernelPower_scaled hz]
  rw [integral_const_mul, ← mul_assoc]
  have he : |z.im| * |z.im| ^ (-(4/3 : ℝ)) = |z.im| ^ (-(1/3 : ℝ)) := by
    calc
      _ = |z.im| ^ (1 : ℝ) * |z.im| ^ (-(4/3 : ℝ)) := by rw [Real.rpow_one]
      _ = |z.im| ^ ((1 : ℝ) + -(4/3 : ℝ)) := (Real.rpow_add hδ _ _).symm
      _ = _ := by norm_num
  rw [he]
  rfl

end AperyMoments
