import CircleKernel.HarmonicError

noncomputable section
open Filter Asymptotics Finset
open scoped Topology
namespace CircleKernel

theorem harmonicError_step_bigO (M : ℕ) :
    (fun n => harmonicError M (n+1)-harmonicError M n) =O[atTop]
      (fun n : ℕ => 1/(n : ℝ)^(M+1)) := by
  have hi : Tendsto (fun n : ℕ => 1/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one] using inverse_nat_power_limit 1 (by omega)
  have h := ((harmonicDefect_bigO M).comp_tendsto hi).neg_left
  apply h.congr'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (harmonicError_step M n (by omega)).symm
  · apply Filter.Eventually.of_forall
    intro n
    simp only [Function.comp_apply, norm_div, norm_one, Real.norm_natCast, one_div_pow]

theorem harmonicError_bigO (M : ℕ) (hM : 0 < M) :
    harmonicError M =O[atTop] (fun n : ℕ => 1/(n : ℝ)^M) :=
  discrete_tail_bigO _ M hM (harmonicError_limit M) (harmonicError_step_bigO M)

/-- Uniform in the discrete index, to every prescribed algebraic order. -/
theorem harmonic_all_order (M : ℕ) (hM : 0 < M) :
    (fun n : ℕ => (harmonic n : ℝ)-Real.log n-Real.eulerMascheroniConstant +
      ∑ j ∈ range M, (bernoulli (j+1) : ℝ)/(j+1)/(n : ℝ)^(j+1)) =O[atTop]
        (fun n : ℕ => 1/(n : ℝ)^M) := by
  exact (harmonicError_bigO M hM).congr_left (fun n => rfl)

end CircleKernel
