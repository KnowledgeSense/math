import AperyMoments.CauchyGluing
import AperyMoments.AuxiliaryHolomorphy

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

theorem analyticAt_lipschitz_closedBall {F : ℂ → ℂ} {a : ℂ} (hA : AnalyticAt ℂ F a)
    {R : ℝ} (hR : 0 < R) : ∃ r : ℝ, 0 < r ∧ 2*r < R ∧
      ∃ K : NNReal, LipschitzOnWith K F (closedBall a (2*r)) := by
  obtain ⟨K, s, hs, hK⟩ := (hA.contDiffAt (n := 1)).exists_lipschitzOnWith
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hs
  let r := min ε R / 4
  have hp : 0 < r := by dsimp [r]; positivity
  have he : 2*r < ε := by dsimp [r]; have := min_le_left ε R; linarith
  have hrr : 2*r < R := by dsimp [r]; have := min_le_right ε R; linarith
  refine ⟨r, hp, hrr, K, hK.mono ?_⟩
  exact (closedBall_subset_ball he).trans hsub

def spectralLocalExtension (b a r : ℝ) : ℂ → ℂ :=
  cauchyLocalExtension (spectralDensity b) (reflectedAuxiliary b) a r

theorem spectralLocalExtension_upper (b a r : ℝ) {z : ℂ} (hz : 0 < z.im) :
    spectralLocalExtension b a r z = spectralCauchyTransform b z :=
  cauchyLocalExtension_upper _ _ _ _ hz

theorem spectralLocalExtension_lower (b a r : ℝ) {z : ℂ} (hz : z.im < 0) :
    spectralLocalExtension b a r z = spectralCauchyTransform b z -
      2 * Real.pi * Complex.I * continuedAuxiliary b z := by
  rw [spectralLocalExtension, cauchyLocalExtension_lower _ _ _ _ hz, reflectedAuxiliary_lower hz]
  rfl

/-- The jump correction is a genuine analytic continuation of the spectral Cauchy transform. -/
theorem spectralLocalExtension_exists {b a : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    (ha : |a| < b) : ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℂ (spectralLocalExtension b a r) (ball (a : ℂ) r) := by
  have hAa := reflectedAuxiliary_analyticOnNhd hb hb2 (a : ℂ)
    ((real_mem_ball_zero_iff a b).mpr ha)
  obtain ⟨r, hr, hrr, K, hK⟩ := analyticAt_lipschitz_closedBall hAa (sub_pos.mpr ha)
  refine ⟨r, hr, cauchyLocalExtension_analyticOnNhd (spectralDensity_measurable b)
    (spectralDensity_integrable hb.le) hr hK ?_ ?_⟩
  · intro z hz
    apply reflectedAuxiliary_analyticOnNhd hb hb2 z
    rw [mem_ball, dist_zero_right]
    have hn : ‖z - (a : ℂ)‖ < r := by simpa only [mem_ball, dist_eq_norm] using hz
    have hs := norm_add_le (z - (a : ℂ)) (a : ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at hs
    linarith
  · intro t _
    exact (reflectedAuxiliary_ofReal b t).symm

end AperyMoments
