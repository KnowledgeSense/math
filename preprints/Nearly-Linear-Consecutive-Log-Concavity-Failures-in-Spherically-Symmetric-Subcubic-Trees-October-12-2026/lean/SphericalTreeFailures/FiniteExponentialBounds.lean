import SphericalTreeFailures.ReverseCoefficients
import Mathlib.Analysis.Complex.Exponential

namespace SphericalTreeFailures
open Finset

theorem factorial_linear_le_double (j : ℕ) :
    (Nat.factorial j : ℝ) ≤ Nat.factorial (2 * j) := by
  exact_mod_cast Nat.factorial_le (by omega : j ≤ 2 * j)

theorem oddReverseCoefficient_exponential_bound (k j : ℕ) :
    oddReverseCoefficient k j ≤ (reverseScale k : ℝ) ^ j / (Nat.factorial j : ℝ) :=
  (oddReverseCoefficient_bound k j).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity) (factorial_linear_le_double j))

theorem evenReverseCoefficient_exponential_bound (k j : ℕ) :
    evenReverseCoefficient k j ≤ (reverseScale k : ℝ) ^ j / (Nat.factorial j : ℝ) :=
  (evenReverseCoefficient_bound k j).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity) (factorial_linear_le_double j))

theorem finite_exponential_bound {c : ℕ → ℝ} {D y : ℝ} (hD : 0 ≤ D) (hy : 0 ≤ y)
    (hc : ∀ j, c j ≤ D ^ j / (Nat.factorial j : ℝ)) (N : ℕ) :
    ∑ j ∈ range N, c j * y ^ j ≤ Real.exp (D * y) := by
  apply le_trans (sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hc j) (pow_nonneg hy j)))
  convert Real.sum_le_exp_of_nonneg (mul_nonneg hD hy) N using 1
  apply sum_congr rfl
  intro j hj
  rw [mul_pow]
  ring

theorem weighted_exponential_sum_bound {z : ℝ} (hz : 0 ≤ z) (N : ℕ) :
    ∑ j ∈ range N, (j : ℝ) * z ^ j / (Nat.factorial j : ℝ) ≤ z * Real.exp z := by
  cases N with
  | zero => simp; positivity
  | succ N =>
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
    have he : ∀ j : ℕ, ((j + 1 : ℕ) : ℝ) * z ^ (j + 1) /
        (Nat.factorial (j + 1) : ℝ) = z * (z ^ j / (Nat.factorial j : ℝ)) := by
      intro j
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    simp_rw [he]
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hz N) hz

theorem finite_weighted_exponential_bound {c : ℕ → ℝ} {D y : ℝ}
    (hD : 0 ≤ D) (hy : 0 ≤ y)
    (hc : ∀ j, c j ≤ D ^ j / (Nat.factorial j : ℝ)) (N : ℕ) :
    ∑ j ∈ range N, (j : ℝ) * c j * y ^ j ≤ D * y * Real.exp (D * y) := by
  apply le_trans (sum_le_sum (fun j hj =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hc j) (Nat.cast_nonneg j)) (pow_nonneg hy j)))
  convert weighted_exponential_sum_bound (mul_nonneg hD hy) N using 1
  apply sum_congr rfl
  intro j hj
  rw [mul_pow]
  ring

end SphericalTreeFailures
