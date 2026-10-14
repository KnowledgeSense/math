import SphericalTreeFailures.PathPolynomial
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SphericalTreeFailures

noncomputable def oddReverseCoefficient (k j : ℕ) : ℝ := Nat.choose (k + 1 + j) (2 * j)
noncomputable def evenReverseCoefficient (k j : ℕ) : ℝ :=
  (Nat.choose (k + 1 + j) (2 * j + 1) : ℝ) / (k + 1)
def reverseScale (k : ℕ) : ℕ := 4 * (k + 1) ^ 2

@[simp] theorem oddReverseCoefficient_zero (k : ℕ) : oddReverseCoefficient k 0 = 1 := by
  simp [oddReverseCoefficient]
@[simp] theorem evenReverseCoefficient_zero (k : ℕ) : evenReverseCoefficient k 0 = 1 := by
  have h : (k : ℝ) + 1 ≠ 0 := by positivity
  simp [evenReverseCoefficient, h]

theorem reverseScale_power (k j : ℕ) :
    (2 * (k + 1 : ℝ)) ^ (2 * j) = (reverseScale k : ℝ) ^ j := by
  rw [pow_mul]
  congr 1
  simp only [reverseScale, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  ring

theorem oddReverseCoefficient_bound (k j : ℕ) :
    oddReverseCoefficient k j ≤ (reverseScale k : ℝ) ^ j / (Nat.factorial (2 * j) : ℝ) := by
  by_cases hj : j ≤ k + 1
  · have h := Nat.choose_le_pow_div (α := ℝ) (2 * j) (k + 1 + j)
    have hn : ((k + 1 + j : ℕ) : ℝ) ≤ 2 * (k + 1 : ℝ) := by exact_mod_cast (by omega : k + 1 + j ≤ 2 * (k + 1))
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (k + 1 + j : ℕ)) hn (2 * j)
    have hd := div_le_div_of_nonneg_right hp (by positivity : (0 : ℝ) ≤ (Nat.factorial (2 * j) : ℝ))
    rw [reverseScale_power] at hd
    exact h.trans hd
  · have hz : Nat.choose (k + 1 + j) (2 * j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [oddReverseCoefficient, hz, Nat.cast_zero]
    positivity

theorem evenReverseCoefficient_bound (k j : ℕ) :
    evenReverseCoefficient k j ≤ (reverseScale k : ℝ) ^ j / (Nat.factorial (2 * j) : ℝ) := by
  cases j with
  | zero => simp
  | succ j =>
    by_cases hj : j + 1 ≤ k
    · have hk : (0 : ℝ) < k + 1 := by positivity
      have hf : (0 : ℝ) < (Nat.factorial (2 * (j + 1)) : ℝ) := by positivity
      have h := Nat.choose_le_pow_div (α := ℝ) (2 * (j + 1) + 1) (k + 1 + (j + 1))
      have hn : ((k + 1 + (j + 1) : ℕ) : ℝ) ≤ 2 * (k + 1 : ℝ) := by exact_mod_cast (by omega : k + 1 + (j + 1) ≤ 2 * (k + 1))
      have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (k + 1 + (j + 1) : ℕ)) hn (2 * (j + 1) + 1)
      have hh := h.trans (div_le_div_of_nonneg_right hp (by positivity))
      rw [le_div_iff₀ (by positivity)] at hh
      rw [pow_succ, reverseScale_power, Nat.factorial_succ] at hh
      push_cast at hh
      unfold evenReverseCoefficient
      apply (div_le_div_iff₀ hk hf).mpr
      have hc : (0 : ℝ) ≤ (Nat.choose (k + 1 + (j + 1)) (2 * (j + 1) + 1) : ℝ) := Nat.cast_nonneg _
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      have hp0 := mul_nonneg hc (le_of_lt hf)
      have hjp := mul_nonneg hj0 hp0
      nlinarith
    · have hz : Nat.choose (k + 1 + (j + 1)) (2 * (j + 1) + 1) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      simp only [evenReverseCoefficient, hz, Nat.cast_zero, zero_div]
      positivity

end SphericalTreeFailures
