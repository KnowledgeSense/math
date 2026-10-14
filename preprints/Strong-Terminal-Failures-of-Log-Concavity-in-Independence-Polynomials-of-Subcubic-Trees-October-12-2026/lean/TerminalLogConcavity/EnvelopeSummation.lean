import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace TerminalLogConcavity
open scoped BigOperators

theorem quarter_geometric_identity (n : ℕ) :
    3 * (∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k) =
      4 * (1 - (1 / 4 : ℝ) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith

theorem quarter_geometric_bound (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k) ≤ 4 / 3 := by
  have h := quarter_geometric_identity n
  have hp : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
  linarith

theorem finite_envelope_bound {L W ρ : ℝ} {n : ℕ} {f : ℕ → ℝ}
    (hL : 0 ≤ L) (hW : 0 ≤ W) (hρ : 0 ≤ ρ)
    (hsmall : W * ρ ≤ 1 / 4)
    (hf : ∀ k < n, f k ≤ ρ ^ k * L) :
    (∑ k ∈ Finset.range n, W ^ k * f k) ≤ (4 / 3) * L := by
  calc
    _ ≤ ∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k * L := by
      apply Finset.sum_le_sum
      intro k hk
      have h1 := mul_le_mul_of_nonneg_left (hf k (Finset.mem_range.mp hk))
        (pow_nonneg hW k)
      have h2 : (W * ρ) ^ k ≤ (1 / 4 : ℝ) ^ k :=
        pow_le_pow_left₀ (mul_nonneg hW hρ) hsmall k
      have h3 := mul_le_mul_of_nonneg_right h2 hL
      rw [mul_pow] at h3
      nlinarith
    _ = (∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k) * L := by rw [Finset.sum_mul]
    _ ≤ (4 / 3) * L := mul_le_mul_of_nonneg_right (quarter_geometric_bound n) hL

end TerminalLogConcavity
