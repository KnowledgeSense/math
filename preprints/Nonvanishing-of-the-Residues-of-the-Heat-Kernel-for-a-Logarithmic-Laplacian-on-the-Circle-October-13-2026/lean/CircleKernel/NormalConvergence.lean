import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open Filter
open scoped Topology
namespace CircleKernel

/-- Finite initial terms do not affect a local summable holomorphic majorant. -/
theorem differentiableAt_tsum_eventual_bound (F : ℕ → ℂ → ℂ)
    (hF : ∀ n, Differentiable ℂ (F n)) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (u : ℕ → ℝ) (hu : Summable u) (N : ℕ)
    (hb : ∀ n, N ≤ n → ∀ w ∈ Metric.ball z r, ‖F n w‖ ≤ u n) :
    DifferentiableAt ℂ (fun w => ∑' n, F n w) z := by
  choose B hB using fun n : ℕ => (isCompact_closedBall z r).exists_bound_of_continuousOn
    (hF n).continuous.continuousOn
  let v : ℕ → ℝ := fun n => if n < N then B n else u n
  have hv : Summable v := by
    apply hu.congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [v, show ¬ n < N by omega]
  have hd := Complex.differentiableOn_tsum_of_summable_norm (U := Metric.ball z r) hv
    (fun n => (hF n).differentiableOn) Metric.isOpen_ball (fun n w hw => ?_)
  · exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by simpa using hr))
  · dsimp [v]
    split_ifs with hn
    · exact hB n w (Metric.ball_subset_closedBall hw)
    · exact hb n (by omega) w hw

end CircleKernel
