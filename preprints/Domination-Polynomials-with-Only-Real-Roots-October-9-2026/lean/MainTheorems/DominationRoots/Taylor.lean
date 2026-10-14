import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace ResearchMain.DominationRoots

open Set

noncomputable def expPartial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), x ^ k / (k.factorial : ℝ)

theorem expPartial_zero (n : ℕ) : expPartial n 0 = 1 := by
  unfold expPartial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    simp [zero_pow hk0]
  · simp

theorem iteratedDeriv_exp (n : ℕ) : iteratedDeriv n Real.exp = Real.exp := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]

theorem exp_taylor_eq (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    taylorWithinEval Real.exp n (uIcc 0 x) 0 x = expPartial n x := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx.symm)
    Real.contDiff_exp.contDiffAt (left_mem_uIcc), iteratedDeriv_exp]
  simp [div_eq_mul_inv, mul_comm]

theorem odd_expPartial_le (m : ℕ) (x : ℝ) : expPartial (2 * m + 1) x ≤ Real.exp x := by
  by_cases hx : x = 0
  · simp [hx, expPartial_zero]
  · obtain ⟨y, hy, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.exp) (n := 2 * m + 1) (Ne.symm hx) Real.contDiff_exp.contDiffOn
    rw [exp_taylor_eq _ hx, iteratedDeriv_exp, sub_zero] at h
    have hp : 0 ≤ x ^ (2 * m + 1 + 1) := by
      convert sq_nonneg (x ^ (m + 1)) using 1
      rw [← pow_mul]
      congr 1
      omega
    have hr : 0 ≤ Real.exp y * x ^ (2 * m + 1 + 1) /
        ((2 * m + 1 + 1).factorial : ℝ) := by positivity
    linarith

theorem expPartial_nineteen_le (x : ℝ) : expPartial 19 x ≤ Real.exp x := by
  exact odd_expPartial_le 9 x

end ResearchMain.DominationRoots
