import MainTheorems.Chollet.BorderSchur
import Mathlib.Algebra.Polynomial.Derivative

noncomputable section

namespace ResearchMain.Chollet

variable {I : Type*} [Fintype I] [DecidableEq I]

def rankPolynomial (B : Matrix I I ℂ) (x : I → ℂ) : Polynomial ℂ :=
  Matrix.permanent (fun i j => Polynomial.C (B i j) +
    Polynomial.X * Polynomial.C (x i * star (x j)))

def rankCoefficient (B : Matrix I I ℂ) (x : I → ℂ) (k : ℕ) : ℝ :=
  ((rankPolynomial B x).coeff k).re

def rankFirst (B : Matrix I I ℂ) (x : I → ℂ) : ℂ :=
  ∑ π : Equiv.Perm I, ∑ i, x (π i) * star (x i) *
    ∏ j ∈ Finset.univ.erase i, B (π j) j

theorem rankPolynomial_eval (B : Matrix I I ℂ) (x : I → ℂ) (s : ℂ) :
    (rankPolynomial B x).eval s =
      Matrix.permanent (fun i j => B i j + s * (x i * star (x j))) := by
  simp only [rankPolynomial, Matrix.permanent, Polynomial.eval_finsetSum,
    Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

theorem rankPolynomial_coeff_zero (B : Matrix I I ℂ) (x : I → ℂ) :
    (rankPolynomial B x).coeff 0 = B.permanent := by
  rw [Polynomial.coeff_zero_eq_eval_zero, rankPolynomial_eval]
  simp

theorem rankCoefficient_zero (B : Matrix I I ℂ) (x : I → ℂ) :
    rankCoefficient B x 0 = B.permanent.re := by
  rw [rankCoefficient, rankPolynomial_coeff_zero]

theorem rankPolynomial_derivative_zero (B : Matrix I I ℂ) (x : I → ℂ) :
    (rankPolynomial B x).derivative.eval 0 = rankFirst B x := by
  simp only [rankPolynomial, rankFirst, Matrix.permanent,
    Polynomial.derivative_sum, Polynomial.derivative_prod_finset,
    Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
    Polynomial.derivative_X, zero_add, mul_zero, add_zero, one_mul,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rankPolynomial_coeff_one (B : Matrix I I ℂ) (x : I → ℂ) :
    (rankPolynomial B x).coeff 1 = rankFirst B x := by
  have h := Polynomial.coeff_derivative (rankPolynomial B x) 0
  rw [Polynomial.coeff_zero_eq_eval_zero, rankPolynomial_derivative_zero] at h
  simpa using h.symm

theorem rankCoefficient_one (B : Matrix I I ℂ) (x : I → ℂ) :
    rankCoefficient B x 1 = (rankFirst B x).re := by
  rw [rankCoefficient, rankPolynomial_coeff_one]

end ResearchMain.Chollet
