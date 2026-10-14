import AperyMoments.CauchyRemainder

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

theorem localCauchyRemainder_continuousAt {F : ℂ → ℂ} {a r : ℝ} (hr : 0 < r) {K : NNReal}
    (hF : LipschitzOnWith K F (closedBall (a : ℂ) (2 * r)))
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball (a : ℂ) r) :
    ContinuousAt (localCauchyRemainder F a r) z₀ := by
  have hFr : ContinuousOn (fun t : ℝ => F (t : ℂ)) (Ioc (a - r) (a + r)) := by
    apply hF.continuousOn.comp (by fun_prop)
    intro t ht
    exact (closedBall_subset_closedBall (by linarith : r ≤ 2 * r))
      (real_interval_mem_closedBall hr.le ⟨ht.1.le, ht.2⟩)
  have hFa : ContinuousAt F z₀ := hF.continuousOn.continuousAt
    (mem_of_superset (isOpen_ball.mem_nhds hz₀)
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith : r ≤ 2 * r))))
  change Tendsto _ _ _
  unfold localCauchyRemainder
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (K : ℝ))
  · apply Eventually.of_forall
    intro z
    rw [uIoc_of_le (by linarith : a - r ≤ a + r)]
    exact ((hFr.aestronglyMeasurable measurableSet_Ioc).sub aestronglyMeasurable_const).mul
      ((show Measurable (fun t : ℝ => (z - (t : ℂ))⁻¹) by fun_prop).aestronglyMeasurable)
  · filter_upwards [isOpen_ball.mem_nhds hz₀] with z hz
    apply Eventually.of_forall
    intro t ht
    rw [uIoc_of_le (by linarith : a - r ≤ a + r)] at ht
    apply localCauchy_quotient_bound hF
    · exact (closedBall_subset_closedBall (by linarith : r ≤ 2 * r)) (ball_subset_closedBall hz)
    · exact (closedBall_subset_closedBall (by linarith : r ≤ 2 * r))
        (real_interval_mem_closedBall hr.le ⟨ht.1.le, ht.2⟩)
  · exact intervalIntegrable_const
  · have hne : ∀ᵐ t : ℝ ∂volume, t ≠ z₀.re := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton z₀.re : volume {z₀.re} = 0)
    filter_upwards [hne] with t ht _
    have hden : z₀ - (t : ℂ) ≠ 0 := by
      intro he
      have hre := congrArg Complex.re he
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
      exact ht (sub_eq_zero.mp hre).symm
    exact ((continuousAt_const.sub hFa).div (by fun_prop) hden).tendsto

end AperyMoments
