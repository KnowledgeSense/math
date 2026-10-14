import TerminalLogConcavity.OrderBound
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace TerminalLogConcavity
open scoped BigOperators

def squareSum (q : ℕ) : ℕ := ∑ i ∈ Finset.range q, (i + 1) ^ 2

theorem squareSum_le_cube (q : ℕ) : squareSum q ≤ q ^ 3 := by
  unfold squareSum
  calc
    _ ≤ ∑ _i ∈ Finset.range q, q ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.pow_le_pow_left (by have := Finset.mem_range.mp hi; omega) 2
    _ = q ^ 3 := by simp; ring

def blockParameterSum (q : ℕ) : ℕ := 16 * q ^ 4 - 7 * q ^ 3 + q ^ 2 + squareSum q

theorem blockParameterSum_lt {q : ℕ} (hq : 2 ≤ q) : blockParameterSum q < 16 * q ^ 4 := by
  have hsq : 0 < q ^ 2 := by positivity
  have hpow : q ^ 2 ≤ q ^ 3 := by nlinarith
  have hfour : 7 * q ^ 3 ≤ 16 * q ^ 4 := by nlinarith
  have hsub := Nat.sub_add_cancel hfour
  have hs := squareSum_le_cube q
  unfold blockParameterSum
  omega

theorem order_bound_from_count_identity {q H h N : ℕ} (hq : 2 ≤ q) (hHpos : 1 ≤ H)
    (hH : H ≤ 2 ^ h)
    (hcount : N + 7 * q ^ 2 + 2 =
      4 * 2 ^ thresholdIndex (target q H) * blockParameterSum q + 4 * q) :
    N ≤ 1200 * q ^ 4 * (q + h) := by
  apply order_bound_from_block_sum hq hHpos hH (blockParameterSum_lt hq)
  nlinarith

end TerminalLogConcavity
