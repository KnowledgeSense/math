import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith

namespace TerminalLogConcavity
open scoped BigOperators

/-- Coefficients of a product of geometric series with the listed ratios. -/
def geometricCoefficient : List ℕ → ℕ → ℕ
  | [], n => if n = 0 then 1 else 0
  | d :: ds, n => ∑ k ∈ Finset.range (n + 1), d ^ k * geometricCoefficient ds (n - k)

theorem geometricCoefficient_le (ds : List ℕ) (n : ℕ) :
    geometricCoefficient ds n ≤ ds.sum ^ n := by
  induction ds generalizing n with
  | nil => cases n <;> simp [geometricCoefficient]
  | cons d ds ih =>
    rw [geometricCoefficient, List.sum_cons, add_pow]
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
    have hchoose : 1 ≤ n.choose k := Nat.choose_pos hk'
    calc
      _ ≤ d ^ k * ds.sum ^ (n - k) := Nat.mul_le_mul_left _ (ih _)
      _ ≤ _ := by
        simpa using Nat.mul_le_mul_left (d ^ k * ds.sum ^ (n - k)) hchoose

end TerminalLogConcavity
