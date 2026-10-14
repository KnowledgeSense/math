import CircleKernel.SpectralMajorant
import CircleKernel.NormalConvergence
import Mathlib.Analysis.PSeries

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace CircleKernel

def spectralRemainder (M : ℕ) (t : ℂ) : ℂ := ∑' n : ℕ, spectralRemainderTerm M (n+1) t

theorem spectralRemainder_summable (M : ℕ) (hM : 0 < M) (t : ℂ)
    (ht : 1 < 2*t.re+(M : ℝ)) : Summable (fun n : ℕ => spectralRemainderTerm M (n+1) t) := by
  obtain ⟨C,hC,N,h⟩ := spectralRemainderTerm_bound M hM ‖t‖ (norm_nonneg _)
  have hu : Summable (fun n : ℕ => C*((n+1 : ℕ) : ℝ)^(-2*t.re-(M : ℝ))) := by
    exact ((Real.summable_nat_rpow.mpr (by linarith)).comp_injective Nat.succ_injective).mul_left C
  apply Summable.of_norm_bounded_eventually_nat hu
  filter_upwards [eventually_ge_atTop N] with n hn
  exact h (n+1) (by omega) t le_rfl t.re le_rfl

theorem spectralRemainder_differentiableAt (M : ℕ) (hM : 0 < M) (t : ℂ)
    (ht : 1 < 2*t.re+(M : ℝ)) : DifferentiableAt ℂ (spectralRemainder M) t := by
  let σ : ℝ := (t.re+(1-(M : ℝ))/2)/2
  let r : ℝ := (t.re-σ)/2
  have hr : 0 < r := by dsimp [r,σ]; linarith
  have hσ : 1 < 2*σ+(M : ℝ) := by dsimp [σ]; linarith
  let R : ℝ := ‖t‖+r
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨C,hC,N,h⟩ := spectralRemainderTerm_bound M hM R hR
  have hu : Summable (fun n : ℕ => C*((n+1 : ℕ) : ℝ)^(-2*σ-(M : ℝ))) := by
    exact ((Real.summable_nat_rpow.mpr (by linarith)).comp_injective Nat.succ_injective).mul_left C
  apply differentiableAt_tsum_eventual_bound (fun n => spectralRemainderTerm M (n+1))
    (fun n => spectralRemainderTerm_differentiable M (n+1)) t r hr _ hu N
  intro n hn w hw
  have hdist : ‖w-t‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hwR : ‖w‖ ≤ R := by
    have hnorm := norm_add_le (w-t) t
    rw [sub_add_cancel] at hnorm
    dsimp [R]
    linarith
  have hwσ : σ ≤ w.re := by
    have hnorm := Complex.re_le_norm (t-w)
    rw [Complex.sub_re, norm_sub_rev] at hnorm
    dsimp [r] at hdist hr
    linarith
  exact h (n+1) (by omega) w hwR σ hwσ

end CircleKernel
