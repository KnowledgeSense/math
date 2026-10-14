import CircleKernel.DefectRemainder
import CircleKernel.PowerBarrier
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

noncomputable section
open Filter Asymptotics Finset
open scoped Topology
namespace CircleKernel

def harmonicError (M n : ℕ) : ℝ :=
  (harmonic n : ℝ)-Real.log n-Real.eulerMascheroniConstant +
    ∑ j ∈ range M, (bernoulli (j+1) : ℝ)/(j+1)/(n : ℝ)^(j+1)

theorem harmonicError_limit (M : ℕ) : Tendsto (harmonicError M) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => ∑ j ∈ range M,
      (bernoulli (j+1) : ℝ)/(j+1)/(n : ℝ)^(j+1)) atTop (𝓝 0) := by
    have ht : ∀ j ∈ range M, Tendsto (fun n : ℕ =>
        (bernoulli (j+1) : ℝ)/(j+1)/(n : ℝ)^(j+1)) atTop (𝓝 0) := by
      intro j hj
      simpa only [mul_zero, mul_one_div] using
        (inverse_nat_power_limit (j+1) (by omega)).const_mul
          ((bernoulli (j+1) : ℝ)/(j+1))
    simpa using tendsto_finsetSum (range M) ht
  have h := (Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant).add hs
  convert h using 1
  · funext n
    simp only [harmonicError]
  · simp

theorem reciprocal_shift_power (x : ℝ) (hx : x ≠ 0) (k : ℕ) :
    (1/x)^k * (1/(1+1/x)^k-1) = 1/(x+1)^k-1/x^k := by
  have hf : (1/x)/(1+1/x) = 1/(x+1) := by
    field_simp
  rw [mul_sub, mul_one, mul_one_div, ← div_pow, hf]
  simp only [one_div_pow]


theorem harmonicError_step (M n : ℕ) (hn : 0 < n) :
    harmonicError M (n+1)-harmonicError M n = -harmonicDefect M (1/(n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
  have hlog : Real.log ((n : ℝ)+1)-Real.log n = Real.log (1+1/(n : ℝ)) := by
    rw [← Real.log_div hn1 hn0]
    congr 1
    field_simp
  have hfrac : (1/(n : ℝ))/(1+1/(n : ℝ)) = 1/((n : ℝ)+1) := by field_simp
  have hsum : (∑ j ∈ range M, (bernoulli (j+1) : ℝ)/(j+1)/((n : ℝ)+1)^(j+1)) -
      (∑ j ∈ range M, (bernoulli (j+1) : ℝ)/(j+1)/(n : ℝ)^(j+1)) =
      -(∑ j ∈ range M, (-(bernoulli (j+1) : ℝ)/(j+1)) * (1/(n : ℝ))^(j+1) *
        (1/(1+1/(n : ℝ))^(j+1)-1)) := by
    rw [← sum_sub_distrib, ← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    rw [mul_assoc, reciprocal_shift_power _ hn0]
    ring
  simp only [harmonicError, harmonicDefect, harmonic_succ, Rat.cast_add, Rat.cast_inv,
    Rat.cast_natCast, Nat.cast_add, Nat.cast_one, hfrac]
  linear_combination hsum-hlog

end CircleKernel
