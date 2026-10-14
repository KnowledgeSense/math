import ArithmeticSections.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ArithmeticSections

/-- The threshold grows by less than a factor of two every two indices. -/
theorem tailThreshold_step (j : ℕ) (hj : 256 ≤ j) :
    tailThreshold (j + 2) < 2 * tailThreshold j := by
  have h : 16 * ((j + 2 + 4) ^ 2 + 2) ≤ 17 * ((j + 4) ^ 2 + 2) := by nlinarith
  have hp := Nat.pow_le_pow_left h 4
  have he : 16 ^ 4 * ((j + 2 + 4) ^ 2 + 2) ^ 4 ≤
      17 ^ 4 * ((j + 4) ^ 2 + 2) ^ 4 := by
    simpa only [Nat.mul_pow] using hp
  have hz : 0 < ((j + 4) ^ 2 + 2) ^ 4 := by positivity
  unfold tailThreshold
  nlinarith

/-- Lemma 4.1, for every integer index in its full range. -/
theorem tailThreshold_lt_exponential (j : ℕ) (hj : 256 ≤ j) :
    72 * tailThreshold j < 2 ^ (j / 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction n using Nat.twoStepInduction with
  | zero => norm_num [tailThreshold]
  | one => norm_num [tailThreshold]
  | more n hn _ =>
    have hs := tailThreshold_step (256 + n) (by omega)
    have he : (256 + (n + 2)) / 2 = (256 + n) / 2 + 1 := by omega
    rw [he, pow_succ]
    have hi : tailThreshold (256 + (n + 2)) < 2 * tailThreshold (256 + n) := by
      simpa only [Nat.add_assoc] using hs
    omega

end ArithmeticSections
