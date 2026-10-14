import AperyMoments.HolomorphicGluing
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology

theorem horizontal_inverse_decomposition (x c : ℝ) :
    ((x:ℂ)+c*I)⁻¹=(x/(c^2+x^2):ℝ)-(c/(c^2+x^2):ℝ)*I := by
  apply Complex.ext <;>
    simp only [Complex.inv_re,Complex.inv_im,Complex.normSq_apply,Complex.add_re,Complex.add_im,
      Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,add_zero,zero_add,sub_zero,zero_sub]
  · congr 1; ring
  · rw [neg_div]; congr 1; ring

theorem horizontal_inverse_integral (a b c : ℝ) (hc : c≠0) :
    (∫ x:ℝ in a..b,((x:ℂ)+c*I)⁻¹)=
      ((Real.log (c^2+b^2)-Real.log (c^2+a^2))/2:ℝ)-
        (Real.arctan (b/c)-Real.arctan (a/c):ℝ)*I := by
  have hn (x:ℝ) : c^2+x^2≠0 := by positivity
  have h1 : Continuous (fun x:ℝ => (x/(c^2+x^2):ℝ)) :=
    continuous_id.div (by fun_prop) hn
  have h2 : Continuous (fun x:ℝ => (c/(c^2+x^2):ℝ)) :=
    continuous_const.div (by fun_prop) hn
  have h1c : IntervalIntegrable (fun x:ℝ => ((x/(c^2+x^2):ℝ):ℂ)) volume a b :=
    (Complex.continuous_ofReal.comp h1).intervalIntegrable a b
  have h2c : IntervalIntegrable (fun x:ℝ => ((c/(c^2+x^2):ℝ):ℂ)*I) volume a b :=
    ((Complex.continuous_ofReal.comp h2).mul continuous_const).intervalIntegrable a b
  simp_rw [horizontal_inverse_decomposition]
  rw [intervalIntegral.integral_sub h1c h2c,
    intervalIntegral.integral_mul_const,intervalIntegral.integral_ofReal,intervalIntegral.integral_ofReal,
    integral_id_div_sq_add_sq hc,integral_div_sq_add_sq]

theorem horizontal_inverse_integral_symmetric (r c : ℝ) (hc : c≠0) :
    (∫ x:ℝ in -r..r,((x:ℂ)+c*I)⁻¹)= -(2*Real.arctan (r/c):ℝ)*I := by
  rw [horizontal_inverse_integral (-r) r c hc]
  simp [neg_div,Real.arctan_neg]
  ring

theorem horizontal_inverse_limit_positive {c : ℝ} (hc : 0<c) :
    Tendsto (fun r:ℝ => ∫ x:ℝ in -r..r,((x:ℂ)+c*I)⁻¹) atTop (𝓝 (-Real.pi*I)) := by
  simp_rw [horizontal_inverse_integral_symmetric _ c (ne_of_gt hc)]
  have h := Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds |>.comp
    (tendsto_id.atTop_div_const hc)
  have hh := ((Complex.continuous_ofReal.tendsto _).comp
    (h.const_mul 2)).neg.mul_const I
  convert hh using 1 <;> norm_num
  ring

theorem horizontal_inverse_limit_negative {c : ℝ} (hc : c<0) :
    Tendsto (fun r:ℝ => ∫ x:ℝ in -r..r,((x:ℂ)+c*I)⁻¹) atTop (𝓝 (Real.pi*I)) := by
  simp_rw [horizontal_inverse_integral_symmetric _ c (ne_of_lt hc)]
  have h := Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds |>.comp
    (tendsto_id.atTop_div_const_of_neg hc)
  have hh := ((Complex.continuous_ofReal.tendsto _).comp
    (h.const_mul 2)).neg.mul_const I
  convert hh using 1 <;> norm_num
  ring

end AperyMoments
