import HilbertBipartite.SquareNumerator
import Mathlib.Algebra.Polynomial.Coeff

open Finset Polynomial
namespace HilbertBipartite

/-- The closed coefficients of the square-maximal-ideal numerator at one. -/
def squareCoefficient (n i : ℕ) : ℕ := 2^(n-2*i) * (n-i).choose i

@[simp] theorem squareCoefficient_zero_index (n : ℕ) : squareCoefficient n 0 = 2^n := by
  simp [squareCoefficient]

theorem squareCoefficient_eq_zero (n i : ℕ) (h : n < 2*i) :
    squareCoefficient n i = 0 := by
  rw [squareCoefficient, Nat.choose_eq_zero_of_lt (by omega : n-i < i), Nat.mul_zero]

theorem squareCoefficient_recurrence (n i : ℕ) :
    squareCoefficient (n+2) (i+1) =
      2*squareCoefficient (n+1) (i+1) + squareCoefficient n i := by
  by_cases h : 2*(i+1) ≤ n+1
  · unfold squareCoefficient
    have he : n+2-(i+1) = (n+1-(i+1))+1 := by omega
    rw [he, Nat.choose_succ_succ]
    rw [show n-i = n+1-(i+1) by omega,
      show n-2*i = n+2-2*(i+1) by omega,
      show n+2-2*(i+1) = n+1-2*(i+1)+1 by omega,
      pow_succ]
    ring
  · by_cases h' : 2*(i+1) ≤ n+2
    · have hn : n = 2*i := by omega
      subst n
      rw [squareCoefficient_eq_zero (2*i+1) (i+1) (by omega)]
      simp only [mul_zero, zero_add, squareCoefficient]
      rw [show 2*i+2-2*(i+1)=0 by omega, show 2*i+2-(i+1)=i+1 by omega,
        show 2*i-2*i=0 by omega, show 2*i-i=i by omega]
      simp
    · rw [squareCoefficient_eq_zero (n+2) (i+1) (by omega),
        squareCoefficient_eq_zero (n+1) (i+1) (by omega),
        squareCoefficient_eq_zero n i (by omega)]

theorem squareNumerator_translated_recurrence (n : ℕ) :
    (squareNumerator (n+2)).comp (1+X) =
      C 2 * (squareNumerator (n+1)).comp (1+X) +
        X * (squareNumerator n).comp (1+X) := by
  simp only [squareNumerator, sub_comp, mul_comp, C_comp, one_comp, X_comp]
  ring

/-- The translated coefficients are the explicit binomial formula, including all zeros. -/
theorem squareNumerator_translated_coeff (n i : ℕ) :
    ((squareNumerator n).comp (1+X)).coeff i = (squareCoefficient n i : ℚ) := by
  induction n using Nat.twoStepInduction generalizing i with
  | zero =>
    cases i with
    | zero => simp [squareNumerator]
    | succ i =>
      rw [squareCoefficient_eq_zero 0 (i+1) (by omega)]
      simp [squareNumerator, coeff_one]
  | one =>
    cases i with
    | zero => simp [squareNumerator]
    | succ i =>
      rw [squareCoefficient_eq_zero 1 (i+1) (by omega)]
      simp [squareNumerator]
  | more n hn hn1 =>
    rw [squareNumerator_translated_recurrence, coeff_add, coeff_C_mul]
    cases i with
    | zero =>
      simp only [coeff_X_mul_zero, add_zero, hn1, squareCoefficient_zero_index]
      push_cast
      ring
    | succ i =>
      simp only [coeff_X_mul, hn, hn1, squareCoefficient_recurrence]
      push_cast
      rfl

end HilbertBipartite
