import TerminalLogConcavity.CoefficientOrder
import Mathlib.Data.Nat.Choose.Sum

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial BigOperators

theorem weighted_binomial_coeff_semiring {R : Type*} [CommSemiring R] (d : R) (q j : ℕ) :
    ((1 + C d * X : R[X]) ^ q).coeff j = (q.choose j : R) * d ^ j := by
  rw [add_comm (1 : R[X]), add_pow, finsetSum_coeff]
  simp only [one_pow, mul_one, mul_pow, ← C_pow, ← C_eq_natCast, coeff_mul_C,
    coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro k _ hk
    simp [hk.symm]
  · intro hj
    have hqj : q < j := by simpa using hj
    simp [Nat.choose_eq_zero_of_lt hqj]

theorem weighted_binomial_coeff (d q j : ℕ) :
    ((1 + C d * X : ℕ[X]) ^ q).coeff j = q.choose j * d ^ j :=
  weighted_binomial_coeff_semiring d q j

end TerminalLogConcavity
