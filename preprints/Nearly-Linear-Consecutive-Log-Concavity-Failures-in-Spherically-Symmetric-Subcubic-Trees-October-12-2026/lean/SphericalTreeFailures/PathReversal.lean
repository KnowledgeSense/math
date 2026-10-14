import SphericalTreeFailures.ReverseCoefficients
import Mathlib.Algebra.Polynomial.Reverse

namespace SphericalTreeFailures
open Polynomial

theorem oddPath_reflect_coeff (k j : ℕ) :
    (reflect (k + 1) (pathPolynomial (2 * k + 1))).coeff j =
      Nat.choose (k + 1 + j) (2 * j) := by
  rw [coeff_reflect]
  by_cases hj : j ≤ k + 1
  · rw [revAt_le hj, pathPolynomial_coeff]
    have he : 2 * k + 1 + 1 - (k + 1 - j) = k + 1 + j := by omega
    rw [he]
    have hs : k + 1 - j = k + 1 + j - 2 * j := by omega
    rw [hs, Nat.choose_symm (by omega : 2 * j ≤ k + 1 + j)]
  · rw [revAt_eq_self_of_lt (by omega), pathPolynomial_coeff]
    rw [Nat.choose_eq_zero_of_lt (by omega : 2 * k + 1 + 1 - j < j),
      Nat.choose_eq_zero_of_lt (by omega : k + 1 + j < 2 * j)]

theorem evenPath_reflect_coeff (k j : ℕ) :
    (reflect k (pathPolynomial (2 * k))).coeff j =
      Nat.choose (k + 1 + j) (2 * j + 1) := by
  rw [coeff_reflect]
  by_cases hj : j ≤ k
  · rw [revAt_le hj, pathPolynomial_coeff]
    have he : 2 * k + 1 - (k - j) = k + 1 + j := by omega
    rw [he]
    have hs : k - j = k + 1 + j - (2 * j + 1) := by omega
    rw [hs, Nat.choose_symm (by omega : 2 * j + 1 ≤ k + 1 + j)]
  · rw [revAt_eq_self_of_lt (by omega), pathPolynomial_coeff]
    rw [Nat.choose_eq_zero_of_lt (by omega : 2 * k + 1 - j < j),
      Nat.choose_eq_zero_of_lt (by omega : k + 1 + j < 2 * j + 1)]

theorem oddPath_natDegree_le (k : ℕ) : (pathPolynomial (2 * k + 1)).natDegree ≤ k + 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [pathPolynomial_coeff]
  exact Nat.choose_eq_zero_of_lt (by omega)

theorem evenPath_natDegree_le (k : ℕ) : (pathPolynomial (2 * k)).natDegree ≤ k := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [pathPolynomial_coeff]
  exact Nat.choose_eq_zero_of_lt (by omega)

end SphericalTreeFailures
