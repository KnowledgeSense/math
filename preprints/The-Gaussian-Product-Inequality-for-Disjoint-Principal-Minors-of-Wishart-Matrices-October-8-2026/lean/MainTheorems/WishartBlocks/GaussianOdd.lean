import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem gaussian_density_reflection_le {μ x : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hμ : 0 ≤ μ) (hx : 0 ≤ x) : gaussianPDFReal μ v (-x) ≤ gaussianPDFReal μ v x := by
  have hv' : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  unfold gaussianPDFReal
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2 * (v : ℝ))
    nlinarith [mul_nonneg hμ hx]
  · positivity

theorem gaussian_odd_integral_nonneg {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (hμ : 0 ≤ μ)
    {f : ℝ → ℝ} (ho : ∀ x, f (-x) = -f x) (hf : ∀ x ≥ 0, 0 ≤ f x)
    (hi : Integrable f (gaussianReal μ v)) :
    0 ≤ ∫ x, f x ∂(gaussianReal μ v) := by
  have hid : Integrable f (volume.withDensity (gaussianPDF μ v)) := by
    rwa [← gaussianReal_of_var_ne_zero μ hv]
  have hiw : Integrable (fun x => gaussianPDFReal μ v x * f x) := by
    simpa only [toReal_gaussianPDF, smul_eq_mul] using
      (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF μ v)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)).mp hid
  have hp : ∀ x ≥ 0, 0 ≤ gaussianPDFReal μ v x * f x +
      gaussianPDFReal μ v (-x) * f (-x) := by
    intro x hx
    have hr := gaussian_density_reflection_le hv hμ hx
    have hn := mul_nonneg (hf x hx) (sub_nonneg.mpr hr)
    rw [ho x]
    nlinarith
  have hn : 0 ≤ ∫ x : ℝ, gaussianPDFReal μ v x * f x +
      gaussianPDFReal μ v (-x) * f (-x) := by
    apply integral_nonneg
    intro x
    change (0 : ℝ) ≤ gaussianPDFReal μ v x * f x + gaussianPDFReal μ v (-x) * f (-x)
    rcases le_total 0 x with hx | hx
    · exact hp x hx
    · simpa only [neg_neg, add_comm] using hp (-x) (neg_nonneg.mpr hx)
  rw [integral_add hiw hiw.comp_neg,
    integral_neg_eq_self (fun x : ℝ => gaussianPDFReal μ v x * f x) volume] at hn
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  linarith

end ResearchMain.WishartBlocks
