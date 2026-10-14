import AperyMoments.CauchyDomain
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

def localCauchyRemainder (F : ℂ → ℂ) (a r : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (a - r)..(a + r), (F (t : ℂ) - F z) / (z - t)

theorem real_interval_mem_closedBall {a r t : ℝ} (_hr : 0 ≤ r) (ht : t ∈ Icc (a - r) (a + r)) :
    (t : ℂ) ∈ closedBall (a : ℂ) r := by
  rw [mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [ht.1, ht.2]

theorem localCauchy_quotient_bound {F : ℂ → ℂ} {a r : ℝ} {K : NNReal}
    (hF : LipschitzOnWith K F (closedBall (a : ℂ) (2 * r)))
    {z : ℂ} (hz : z ∈ closedBall (a : ℂ) (2 * r)) {t : ℝ}
    (ht : (t : ℂ) ∈ closedBall (a : ℂ) (2 * r)) :
    ‖(F (t : ℂ) - F z) / (z - t)‖ ≤ (K : ℝ) := by
  by_cases hzt : z - (t : ℂ) = 0
  · rw [hzt, div_zero, norm_zero]
    exact K.coe_nonneg
  · rw [norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hzt)).mpr
    simpa only [norm_sub_rev] using hF.norm_sub_le ht hz

theorem localCauchyRemainder_boundary {F : ℂ → ℂ} {a r : ℝ} (hr : 0 < r) {K : NNReal}
    (hF : LipschitzOnWith K F (closedBall (a : ℂ) (2 * r))) :
    Tendsto (localCauchyRemainder F a r) (𝓝[{z : ℂ | z.im ≠ 0}] (a : ℂ))
      (𝓝 (localCauchyRemainder F a r (a : ℂ))) := by
  have hFr : ContinuousOn (fun t : ℝ => F (t : ℂ)) (Icc (a - r) (a + r)) := by
    apply hF.continuousOn.comp (by fun_prop)
    intro t ht
    exact (closedBall_subset_closedBall (by linarith : r ≤ 2 * r)) (real_interval_mem_closedBall hr.le ht)
  have hFa : ContinuousAt F (a : ℂ) := hF.continuousOn.continuousAt (closedBall_mem_nhds _ (by linarith : 0 < 2 * r))
  unfold localCauchyRemainder
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (K : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hcont : ContinuousOn (fun t : ℝ => (F (t : ℂ) - F z) / (z - t)) (Icc (a - r) (a + r)) := by
      apply ContinuousOn.div (hFr.sub continuousOn_const) (by fun_prop)
      intro t _ ht
      have he := congrArg Complex.im ht
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at he
      exact hz he
    have hi : IntervalIntegrable (fun t : ℝ => (F (t : ℂ) - F z) / (z - t)) volume (a - r) (a + r) := by
      apply ContinuousOn.intervalIntegrable
      simpa only [uIcc_of_le (by linarith : a - r ≤ a + r)] using hcont
    exact hi.def'.aestronglyMeasurable
  · filter_upwards [nhdsWithin_le_nhds (s := {z : ℂ | z.im ≠ 0}) (ball_mem_nhds (a : ℂ) hr)] with z hz
    apply Eventually.of_forall
    intro t ht
    rw [uIoc_of_le (by linarith : a - r ≤ a + r)] at ht
    apply localCauchy_quotient_bound hF
    · exact (closedBall_subset_closedBall (by linarith : r ≤ 2 * r)) (ball_subset_closedBall hz)
    · exact (closedBall_subset_closedBall (by linarith : r ≤ 2 * r))
        (real_interval_mem_closedBall hr.le ⟨ht.1.le, ht.2⟩)
  · exact intervalIntegrable_const
  · have hne : ∀ᵐ t : ℝ ∂volume, t ≠ a := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton a : volume {a} = 0)
    filter_upwards [hne] with t ht _
    have hden : (a : ℂ) - t ≠ 0 := by
      rw [← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm ht))
    exact ((continuousAt_const.sub hFa).div (by fun_prop) hden).tendsto.mono_left nhdsWithin_le_nhds

end AperyMoments
