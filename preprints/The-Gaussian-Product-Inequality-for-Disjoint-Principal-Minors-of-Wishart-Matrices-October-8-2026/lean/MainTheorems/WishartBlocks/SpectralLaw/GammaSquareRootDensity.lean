import MainTheorems.WishartBlocks.GammaMoments
import Mathlib.MeasureTheory.Function.JacobianOneDim

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def sqrtGammaPDF (a r t : ℝ) : ℝ≥0∞ :=
  if 0 < t then ENNReal.ofReal (2 * t) * gammaPDF a r (t ^ 2) else 0

theorem square_image_positive : (fun t : ℝ => t ^ 2) '' Set.Ioi 0 = Set.Ioi 0 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    change 0 < t at ht
    exact sq_pos_of_pos ht
  · intro hx
    change 0 < x at hx
    exact ⟨Real.sqrt x, Real.sqrt_pos.mpr hx, Real.sq_sqrt hx.le⟩

theorem square_injOn_positive : Set.InjOn (fun t : ℝ => t ^ 2) (Set.Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  change x ^ 2 = y ^ 2 at hxy
  nlinarith

theorem sqrt_gamma_lintegral (a r : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ t, f t ∂(gammaMeasure a r).map Real.sqrt) =
      ∫⁻ t, sqrtGammaPDF a r t * f t := by
  rw [lintegral_map hf Real.continuous_sqrt.measurable]
  have hrestrict : (gammaMeasure a r).restrict (Set.Ioi 0) = gammaMeasure a r :=
    Measure.restrict_eq_self_of_ae_mem (gammaMeasure_ae_positive a r)
  rw [← hrestrict]
  change (∫⁻ t in Set.Ioi 0, f (Real.sqrt t) ∂volume.withDensity (gammaPDF a r)) = _
  rw [setLIntegral_withDensity_eq_setLIntegral_mul volume
    (f := gammaPDF a r) (g := fun t => f (Real.sqrt t))
    (by exact (measurable_gammaPDFReal a r).ennreal_ofReal)
    (hf.comp Real.continuous_sqrt.measurable) measurableSet_Ioi]
  have hderiv (t : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
    have h := (hasDerivAt_id t).pow 2
    change HasDerivAt (fun x : ℝ => x ^ 2) (2 * t ^ (2 - 1) * 1) t at h
    simpa only [Nat.reduceSub, pow_one, mul_one] using h
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun t _ => (hderiv t).hasDerivWithinAt) square_injOn_positive
    (fun x => gammaPDF a r x * f (Real.sqrt x))
  rw [square_image_positive] at hchange
  change (∫⁻ t in Set.Ioi 0, gammaPDF a r t * f (Real.sqrt t)) = _
  rw [hchange]
  have he : (fun t : ℝ => sqrtGammaPDF a r t * f t) =
      (Set.Ioi 0).indicator (fun t => ENNReal.ofReal (2 * t) * gammaPDF a r (t ^ 2) * f t) := by
    funext t
    simp only [sqrtGammaPDF, Set.indicator_apply, Set.mem_Ioi]
    split_ifs <;> simp only [zero_mul]
  rw [he, lintegral_indicator measurableSet_Ioi]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change ENNReal.ofReal |2 * t| * (gammaPDF a r (t ^ 2) * f (Real.sqrt (t ^ 2))) =
    ENNReal.ofReal (2 * t) * gammaPDF a r (t ^ 2) * f t
  rw [abs_of_pos (mul_pos (by norm_num) ht), Real.sqrt_sq ht.le, mul_assoc]

theorem sqrt_gamma_density (a r : ℝ) :
    (gammaMeasure a r).map Real.sqrt = volume.withDensity (sqrtGammaPDF a r) := by
  ext s hs
  have h := sqrt_gamma_lintegral a r (f := s.indicator (fun _ => 1))
    (measurable_const.indicator hs)
  rw [lintegral_indicator hs] at h
  simp only [lintegral_one, Measure.restrict_apply_univ] at h
  rw [withDensity_apply _ hs]
  simpa only [← Set.indicator_mul_right, lintegral_indicator hs, mul_one] using h

end ResearchMain.WishartBlocks
