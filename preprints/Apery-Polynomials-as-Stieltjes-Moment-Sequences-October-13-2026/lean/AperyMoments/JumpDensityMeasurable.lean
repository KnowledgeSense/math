import AperyMoments.MomentJumpDensity

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

theorem latticeExpression_measurable : Measurable latticeExpression := by
  unfold latticeExpression
  exact (ellipticK_measurable.comp (by fun_prop)).div_const _

theorem ellipticKappa_measurable : Measurable ellipticKappa := by
  unfold ellipticKappa
  apply Measurable.ite (measurableSet_le measurable_id measurable_const) ellipticK_measurable
  exact (by fun_prop : Measurable (fun m : ℝ => m ^ (-(1/2 : ℝ)))).mul
    (ellipticK_measurable.comp measurable_inv)

theorem continuedDensity_measurable (b : ℝ) : Measurable (continuedDensity b) := by
  have hm : Measurable (fun p : ℝ × ℝ => latticeExpression (p.1 - b * Real.cos p.2)) :=
    latticeExpression_measurable.comp (by fun_prop)
  have h := hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 Real.pi))
  have he : continuedDensity b = (fun w : ℝ => Real.pi⁻¹ * ∫ θ in Ioc (0 : ℝ) Real.pi,
      latticeExpression (w - b * Real.cos θ)) := by
    funext w
    unfold continuedDensity
    rw [intervalIntegral.integral_of_le Real.pi_pos.le]
  rw [he]
  exact h.measurable.const_mul _

theorem continuationCorrection_measurable (b : ℝ) : Measurable (continuationCorrection b) := by
  let f : ℝ → ℝ → ℝ := fun w u => ellipticKappa ((w-u)^2/16) / Real.sqrt (u^2-b^2)
  have hf : Measurable (Function.uncurry f) :=
    (ellipticKappa_measurable.comp (by fun_prop)).div (by fun_prop)
  have hL : Measurable (fun p : ℝ × ℝ => (Ioc b p.1).indicator (f p.1) p.2) := by
    simp only [indicator_apply, mem_Ioc]
    exact Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)) hf measurable_const
  have hR : Measurable (fun p : ℝ × ℝ => (Ioc p.1 b).indicator (f p.1) p.2) := by
    simp only [indicator_apply, mem_Ioc]
    exact Measurable.ite ((measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)) hf measurable_const
  have hl := (hL.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have hr := (hR.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  simp only [integral_indicator measurableSet_Ioc] at hl hr
  exact (hl.sub hr).const_mul _

theorem reciprocalMomentDensity_measurable (α : ℝ) : Measurable (reciprocalMomentDensity α) := by
  have hr : Measurable (reciprocalRadius α) := by unfold reciprocalRadius; fun_prop
  unfold reciprocalMomentDensity
  apply Measurable.ite ((measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_eq_fun measurable_id measurable_const).compl)
  · apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
    · exact ((spectralDensity_measurable _).comp hr).div (by fun_prop)
    · exact ((((continuedDensity_measurable _).comp hr).const_mul 2).sub
        ((spectralDensity_measurable _).comp hr) |>.add
        (((continuationCorrection_measurable _).comp hr).const_mul 2)).div (by fun_prop)
  · exact measurable_const

end AperyMoments
