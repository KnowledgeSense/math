import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

open MeasureTheory Filter
open scoped Topology

theorem positive_laplace_moment_hasDerivAt {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {a b : X → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (ha0 : ∀ᵐ x ∂μ, 0 ≤ a x) (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x)
    (hi : Integrable b μ) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasDerivAt (fun t : ℝ => ∫ x, Real.exp (-a x - t * b x) ∂μ)
      (∫ x, -b x * Real.exp (-a x - t₀ * b x) ∂μ) t₀ := by
  have ht : ∀ t ∈ Metric.ball t₀ t₀, 0 ≤ t := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have h := (abs_lt.mp ht).1
    linarith
  have hI : Integrable (fun x => Real.exp (-a x - t₀ * b x)) μ := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards [ha0, hb0] with x hax hbx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_one_iff.mpr
    nlinarith
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Metric.ball t₀ t₀) (bound := b)
    (F := fun t x => Real.exp (-a x - t * b x))
    (F' := fun t x => -b x * Real.exp (-a x - t * b x))
    (Metric.ball_mem_nhds t₀ ht₀) _ hI _ _ hi _).2
  · exact Eventually.of_forall fun t => (by fun_prop : Measurable
      (fun x => Real.exp (-a x - t * b x))).aestronglyMeasurable
  · exact (by fun_prop : Measurable
      (fun x => -b x * Real.exp (-a x - t₀ * b x))).aestronglyMeasurable
  · filter_upwards [ha0, hb0] with x hax hbx
    intro t ht'
    have he : Real.exp (-a x - t * b x) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [ht t ht']
    rw [norm_mul, norm_neg, Real.norm_of_nonneg hbx,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he hbx
  · exact ae_of_all _ fun x t _ => by
      have h := ((hasDerivAt_const t (-a x)).sub
        ((hasDerivAt_id' t).mul_const (b x))).exp
      simpa only [Pi.sub_apply, zero_sub, one_mul, mul_one, mul_comm] using h

theorem positive_laplace_moment_hasDerivWithinAt_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {a b : X → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (ha0 : ∀ᵐ x ∂μ, 0 ≤ a x) (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x)
    (hi : Integrable b μ) :
    HasDerivWithinAt (fun t : ℝ => ∫ x, Real.exp (-a x - t * b x) ∂μ)
      (∫ x, -b x * Real.exp (-a x) ∂μ) (Set.Ici 0) 0 := by
  let F : ℝ → ℝ := fun t => ∫ x, Real.exp (-a x - t * b x) ∂μ
  have hC : ContinuousWithinAt F (Set.Ioi 0) 0 := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := μ)
      (l := 𝓝[>] (0 : ℝ)) (bound := fun _ => (1 : ℝ))
      (F := fun t x => Real.exp (-a x - t * b x))
      (f := fun x => Real.exp (-a x))
      (Eventually.of_forall fun t => (by fun_prop : Measurable
        (fun x => Real.exp (-a x - t * b x))).aestronglyMeasurable)
      (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        filter_upwards [ha0, hb0] with x hax hbx
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        apply Real.exp_le_one_iff.mpr
        have ht' : 0 ≤ t := (Set.mem_Ioi.mp ht).le
        nlinarith)
      (integrable_const (1 : ℝ))
      (ae_of_all _ fun x => by
        simpa only [zero_mul, sub_zero] using
          ((by fun_prop : Continuous (fun t : ℝ =>
            Real.exp (-a x - t * b x))).continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds)
    change Tendsto F (𝓝[>] 0) (𝓝 (F 0))
    simpa only [F, zero_mul, sub_zero] using h
  have hD : Tendsto (fun t : ℝ => ∫ x, -b x * Real.exp (-a x - t * b x) ∂μ)
      (𝓝[>] 0) (𝓝 (∫ x, -b x * Real.exp (-a x) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence b
    · exact Eventually.of_forall fun t => (by fun_prop : Measurable
        (fun x => -b x * Real.exp (-a x - t * b x))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with t ht
      filter_upwards [ha0, hb0] with x hax hbx
      have he : Real.exp (-a x - t * b x) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have ht' : 0 ≤ t := (Set.mem_Ioi.mp ht).le
        nlinarith
      rw [norm_mul, norm_neg, Real.norm_of_nonneg hbx,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he hbx
    · exact hi
    · exact ae_of_all _ fun x => by
        simpa only [zero_mul, sub_zero] using
          ((by fun_prop : Continuous (fun t : ℝ =>
            -b x * Real.exp (-a x - t * b x))).continuousAt (x := 0)).tendsto.mono_left
              nhdsWithin_le_nhds
  have hdiff : DifferentiableOn ℝ F (Set.Ioi 0) := by
    intro t ht
    exact (positive_laplace_moment_hasDerivAt μ ha hb ha0 hb0 hi
      (Set.mem_Ioi.mp ht)).differentiableAt.differentiableWithinAt
  have hlimit : Tendsto (fun t => deriv F t) (𝓝[>] 0)
      (𝓝 (∫ x, -b x * Real.exp (-a x) ∂μ)) := by
    apply hD.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (positive_laplace_moment_hasDerivAt μ ha hb ha0 hb0 hi
      (Set.mem_Ioi.mp ht)).deriv.symm
  exact hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hC self_mem_nhdsWithin hlimit

end ResearchMain.WishartBlocks
