import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace TerminalLogConcavity

def sumSquares (xs : List ℕ) : ℕ := (xs.map (fun u => u ^ 2)).sum

theorem length_le_sum_of_positive {xs : List ℕ} (hx : ∀ u ∈ xs, 1 ≤ u) :
    xs.length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons u xs ih =>
    have hu := hx u (by simp)
    have hs := ih (fun v hv => hx v (by simp [hv]))
    simp only [List.length_cons, List.sum_cons]
    omega

/-- The Gaussian penalty from at least two active factors. -/
theorem positive_composition_square_gap {xs : List ℕ} (hx : ∀ u ∈ xs, 1 ≤ u) :
    sumSquares xs + (xs.length - 1) * xs.sum ≤ xs.sum ^ 2 := by
  induction xs with
  | nil => simp [sumSquares]
  | cons u xs ih =>
    have hu := hx u (by simp)
    have hxs : ∀ v ∈ xs, 1 ≤ v := fun v hv => hx v (by simp [hv])
    have hs := ih hxs
    have hlen := length_le_sum_of_positive hxs
    cases xs with
    | nil => simp [sumSquares]
    | cons v vs =>
      have hk : (v :: vs).length - 1 + 1 = (v :: vs).length := by simp
      have hm := Nat.mul_le_mul_left u hlen
      have hm' := Nat.mul_le_mul_right (v :: vs).sum hu
      simp only [sumSquares, List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_sub_cancel] at hs ⊢
      change vs.length + 1 ≤ v + vs.sum at hlen
      change u * (vs.length + 1) ≤ u * (v + vs.sum) at hm
      change 1 * (v + vs.sum) ≤ u * (v + vs.sum) at hm'
      nlinarith

theorem gaussian_exponent_identity (i u : ℤ) :
    2 * i * u - i ^ 2 = u ^ 2 - (i - u) ^ 2 := by ring

end TerminalLogConcavity
