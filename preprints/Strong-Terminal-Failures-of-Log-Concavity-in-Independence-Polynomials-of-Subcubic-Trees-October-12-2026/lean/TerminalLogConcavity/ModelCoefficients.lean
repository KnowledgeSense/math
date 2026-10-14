import TerminalLogConcavity.CoefficientComparison
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

namespace TerminalLogConcavity

theorem choose_square_le_four_adjacent {q j : ℕ} (hj : 1 ≤ j) (hjq : j < q) :
    (q.choose j : ℝ) ^ 2 ≤ 4 * (q.choose (j - 1) : ℝ) * (q.choose (j + 1) : ℝ) := by
  have hm := Nat.choose_succ_right_eq q (j - 1)
  have hp := Nat.choose_succ_right_eq q j
  have he : j - 1 + 1 = j := by omega
  have hd : q - (j - 1) = q - j + 1 := by omega
  rw [he, hd] at hm
  have hmr : (q.choose j : ℝ) * j =
      (q.choose (j - 1) : ℝ) * ((q - j : ℕ) + 1) := by exact_mod_cast hm
  have hpr : (q.choose (j + 1) : ℝ) * (j + 1) =
      (q.choose j : ℝ) * (q - j : ℕ) := by exact_mod_cast hp
  have hrel : (q.choose (j - 1) : ℝ) * (q.choose (j + 1) : ℝ) *
      ((j : ℝ) + 1) * ((q - j : ℕ) + 1) =
      (q.choose j : ℝ) ^ 2 * j * (q - j : ℕ) := by
    calc
      _ = ((q.choose (j - 1) : ℝ) * ((q - j : ℕ) + 1)) *
          ((q.choose (j + 1) : ℝ) * (j + 1)) := by ring
      _ = _ := by rw [← hmr, hpr]; ring
  have hf := adjacent_index_factor hj hjq
  push_cast at hf
  have hn : 0 ≤ (q.choose (j - 1) : ℝ) * (q.choose (j + 1) : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hf hn
  have hpos : 0 < (j : ℝ) * (q - j : ℕ) := by
    have : 0 < q - j := by omega
    positivity
  nlinarith

def modelCoefficient (q K D : ℕ) (a : ℝ) (j : ℕ) : ℝ :=
  (q.choose j : ℝ) * a ^ (K + D * j + j ^ 2)

theorem modelCoefficient_pos {q K D j : ℕ} {a : ℝ} (ha : 0 < a) (hj : j ≤ q) :
    0 < modelCoefficient q K D a j := by
  unfold modelCoefficient
  have : 0 < q.choose j := Nat.choose_pos hj
  positivity

theorem quadratic_exponent_identity (K D j : ℕ) (hj : 1 ≤ j) :
    (K + D * (j - 1) + (j - 1) ^ 2) +
      (K + D * (j + 1) + (j + 1) ^ 2) = 2 + 2 * (K + D * j + j ^ 2) := by
  have he : j = (j - 1) + 1 := by omega
  conv_rhs => rw [he]
  conv_lhs => rhs; rw [he]
  ring

theorem modelCoefficient_curvature {q K D j : ℕ} {a : ℝ}
    (hj : 1 ≤ j) (hjq : j < q) :
    a ^ 2 * modelCoefficient q K D a j ^ 2 ≤
      4 * (modelCoefficient q K D a (j - 1) * modelCoefficient q K D a (j + 1)) := by
  have hexp : a ^ (K + D * (j - 1) + (j - 1) ^ 2) *
      a ^ (K + D * (j + 1) + (j + 1) ^ 2) =
      a ^ 2 * (a ^ (K + D * j + j ^ 2)) ^ 2 := by
    rw [← pow_add, quadratic_exponent_identity K D j hj, pow_add, mul_comm 2, pow_mul]
  have h := mul_le_mul_of_nonneg_right (choose_square_le_four_adjacent hj hjq)
    (mul_nonneg (sq_nonneg a) (sq_nonneg (a ^ (K + D * j + j ^ 2))))
  unfold modelCoefficient
  calc
    _ ≤ 4 * (q.choose (j - 1) : ℝ) * (q.choose (j + 1) : ℝ) *
        (a ^ 2 * (a ^ (K + D * j + j ^ 2)) ^ 2) := by nlinarith [h]
    _ = _ := by rw [← hexp]; ring

end TerminalLogConcavity
