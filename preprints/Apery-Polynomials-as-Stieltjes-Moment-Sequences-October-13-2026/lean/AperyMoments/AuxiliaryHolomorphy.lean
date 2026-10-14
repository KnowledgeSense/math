import AperyMoments.AuxiliaryReflection
import AperyMoments.BoundaryExtension
import AperyMoments.HolomorphicGluing

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

theorem real_mem_ball_zero_iff (a b : ℝ) : (a : ℂ) ∈ ball (0 : ℂ) b ↔ |a| < b := by
  simp [Metric.mem_ball, dist_eq_norm, Complex.norm_real, Real.norm_eq_abs]

theorem reflectedAuxiliary_continuousOn {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 2) :
    ContinuousOn (reflectedAuxiliary b) (ball (0 : ℂ) b) := by
  apply continuousOn_of_halfPlane_limits
  · intro z _ hz
    rcases lt_or_gt_of_ne hz with hz | hz
    · exact (reflectedAuxiliary_lower_differentiableAt hb hz).continuousAt
    · exact (reflectedAuxiliary_upper_differentiableAt hb hz).continuousAt
  · intro a ha
    have h := abs_lt.mp ((real_mem_ball_zero_iff a b).mp ha)
    exact reflectedAuxiliary_lower_boundary hb hb2 h.1 h.2
  · intro a ha
    have h := abs_lt.mp ((real_mem_ball_zero_iff a b).mp ha)
    exact reflectedAuxiliary_upper_boundary hb hb2 h.1 h.2

/-- Actual Schwarz gluing: continuity is derived from both unrestricted boundary limits. -/
theorem reflectedAuxiliary_differentiableOn {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 2) :
    DifferentiableOn ℂ (reflectedAuxiliary b) (ball (0 : ℂ) b) := by
  apply differentiableOn_ball_of_continuousOn_off_real (reflectedAuxiliary_continuousOn hb hb2)
  intro z _ hz
  rcases lt_or_gt_of_ne hz with hz | hz
  · exact reflectedAuxiliary_lower_differentiableAt hb hz
  · exact reflectedAuxiliary_upper_differentiableAt hb hz

theorem reflectedAuxiliary_analyticOnNhd {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 2) :
    AnalyticOnNhd ℂ (reflectedAuxiliary b) (ball (0 : ℂ) b) :=
  (reflectedAuxiliary_differentiableOn hb hb2).analyticOnNhd isOpen_ball

theorem reflectedAuxiliary_even {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 2) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) b) : reflectedAuxiliary b (-z) = reflectedAuxiliary b z := by
  have hf := reflectedAuxiliary_analyticOnNhd hb hb2
  have hg : AnalyticOnNhd ℂ (fun z => reflectedAuxiliary b (-z)) (ball (0 : ℂ) b) := by
    intro z hz
    have hn : -z ∈ ball (0 : ℂ) b := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact (hf (-z) hn).comp (f := fun z : ℂ => -z) (by fun_prop)
  have he := hg.eqOn_of_preconnected_of_mem_closure hf (convex_ball (0 : ℂ) b).isPreconnected
    (z₀ := (0 : ℂ)) (mem_ball_self hb)
  apply he _ hz
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨((ε / 2 : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
  · change reflectedAuxiliary b (-((ε / 2 : ℝ) : ℂ)) = reflectedAuxiliary b ((ε / 2 : ℝ) : ℂ)
    rw [← Complex.ofReal_neg, reflectedAuxiliary_ofReal, reflectedAuxiliary_ofReal, spectralDensity_neg]
  · simp only [mem_singleton_iff]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  · simpa [dist_eq_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε] using
      (show ε / 2 < ε by linarith)

end AperyMoments
