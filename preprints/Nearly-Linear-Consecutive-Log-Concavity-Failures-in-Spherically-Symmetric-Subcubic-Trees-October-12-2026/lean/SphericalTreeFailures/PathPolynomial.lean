import SphericalTreeFailures.Definitions
import Mathlib.Data.Nat.Choose.Basic

namespace SphericalTreeFailures
open Polynomial

noncomputable def pathPolynomial (n : ℕ) : ℕ[X] := (pendantPath n).polynomials.1

theorem pathPolynomial_zero : pathPolynomial 0 = 1 := rfl
theorem pathPolynomial_one : pathPolynomial 1 = 1 + X := by
  simp [pathPolynomial, pendantPath, ForestExpr.polynomials]
theorem pathPolynomial_recursion (n : ℕ) :
    pathPolynomial (n + 2) = pathPolynomial (n + 1) + X * pathPolynomial n := rfl

theorem pathPolynomial_graph (n : ℕ) :
    independencePolynomial (pendantPath n).graph Finset.univ = pathPolynomial n :=
  (pendantPath n).graph_polynomial

theorem path_binomial_recursion (n j : ℕ) :
    Nat.choose (n + 2 - j) (j + 1) =
      Nat.choose (n + 1 - j) (j + 1) + Nat.choose (n + 1 - j) j := by
  by_cases h : j ≤ n + 1
  · have he : n + 2 - j = (n + 1 - j) + 1 := by omega
    rw [he, Nat.choose_succ_succ']
    omega
  · have h1 : n + 1 - j = 0 := by omega
    have h2 : n + 2 - j < j + 1 := by omega
    rw [h1, Nat.choose_eq_zero_of_lt h2, Nat.choose_eq_zero_of_lt (by omega : 0 < j + 1),
      Nat.choose_eq_zero_of_lt (by omega : 0 < j)]

/-- The exact coefficient formula counts independent subsets of the actual path. -/
theorem pathPolynomial_coeff (n j : ℕ) :
    (pathPolynomial n).coeff j = Nat.choose (n + 1 - j) j := by
  induction n using Nat.twoStepInduction generalizing j with
  | zero =>
    cases j with
    | zero => simp [pathPolynomial_zero]
    | succ j => simp [pathPolynomial_zero, coeff_one, Nat.choose_eq_zero_of_lt]
  | one =>
    cases j with
    | zero => simp [pathPolynomial_one, coeff_one, coeff_X]
    | succ j =>
      cases j with
      | zero => simp [pathPolynomial_one, coeff_one, coeff_X]
      | succ j => simp [pathPolynomial_one, coeff_one, coeff_X, Nat.choose_eq_zero_of_lt]
  | more n ih0 ih1 =>
    rw [pathPolynomial_recursion, coeff_add]
    cases j with
    | zero => simp [ih1]
    | succ j =>
      rw [coeff_X_mul, ih1, ih0]
      have h1 : n + 2 + 1 - (j + 1) = n + 2 - j := by omega
      have h2 : n + 1 + 1 - (j + 1) = n + 1 - j := by omega
      rw [h1, h2]
      exact (path_binomial_recursion n j).symm

end SphericalTreeFailures
