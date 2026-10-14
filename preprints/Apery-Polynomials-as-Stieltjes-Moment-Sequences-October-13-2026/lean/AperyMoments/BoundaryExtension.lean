import Mathlib.Topology.DenseEmbedding
import Mathlib.Analysis.Complex.Basic

open Set Filter
open scoped Topology
namespace AperyMoments

theorem nonreal_dense : Dense {z : ℂ | z.im ≠ 0} := by
  rw [Metric.dense_iff]
  intro z r hr
  by_cases hz : z.im = 0
  · refine ⟨z + (r / 2 : ℝ) * Complex.I, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      simpa [norm_mul, abs_of_pos hr] using (show r / 2 < r by linarith)
    · simp only [mem_ofPred_eq, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, hz,
        zero_add]
      exact ne_of_gt (half_pos hr)
  · exact ⟨z, Metric.mem_ball_self hr, hz⟩

/-- Matching limits from both open half-planes give continuity across the real axis. -/
theorem continuousOn_of_halfPlane_limits {F : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hcont : ∀ z ∈ Metric.ball c r, z.im ≠ 0 → ContinuousAt F z)
    (hl : ∀ x : ℝ, (x : ℂ) ∈ Metric.ball c r →
      Tendsto F (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (F (x : ℂ))))
    (hu : ∀ x : ℝ, (x : ℂ) ∈ Metric.ball c r →
      Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (F (x : ℂ)))) :
    ContinuousOn F (Metric.ball c r) := by
  let S : Set ℂ := {z | z.im ≠ 0}
  have hlim : ∀ z ∈ Metric.ball c r, Tendsto F (𝓝[S] z) (𝓝 (F z)) := by
    intro z hz
    by_cases hi : z.im = 0
    · have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
      have hs : S = {z : ℂ | z.im < 0} ∪ {z : ℂ | 0 < z.im} := by
        ext w
        simp only [S, mem_ofPred_eq, mem_union]
        exact ne_iff_lt_or_gt
      rw [hs, nhdsWithin_union]
      have h1 := hl z.re (by simpa [he] using hz)
      have h2 := hu z.re (by simpa [he] using hz)
      simpa only [he] using h1.sup h2
    · exact (hcont z hz hi).tendsto.mono_left nhdsWithin_le_nhds
  have hsub : ∀ z ∈ Metric.ball c r,
      Tendsto (fun w : S => F w) (comap Subtype.val (𝓝 z)) (𝓝 (F z)) := by
    intro z hz
    change Tendsto (F ∘ Subtype.val) _ _
    rw [← tendsto_map'_iff]
    simpa only [map_comap, Subtype.range_val, nhdsWithin] using hlim z hz
  intro z hz
  have hn : Metric.ball c r ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds hz
  have hext : ContinuousAt (nonreal_dense.extend (fun w : S => F w)) z := by
    apply nonreal_dense.continuousAt_extend
    filter_upwards [hn] with w hw
    exact ⟨F w, hsub w hw⟩
  have heq : F =ᶠ[𝓝 z] nonreal_dense.extend (fun w : S => F w) := by
    filter_upwards [hn] with w hw
    exact (nonreal_dense.extend_eq_of_tendsto (hsub w hw)).symm
  exact (hext.congr_of_eventuallyEq heq).continuousWithinAt

end AperyMoments
