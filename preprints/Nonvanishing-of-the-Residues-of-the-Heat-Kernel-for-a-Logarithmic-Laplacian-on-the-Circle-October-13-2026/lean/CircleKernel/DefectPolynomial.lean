import CircleKernel.BernoulliCancellation
import Mathlib.Algebra.Polynomial.Div

noncomputable section
open Finset Polynomial
namespace CircleKernel

def inverseTaylor (k M : ℕ) : ℚ[X] :=
  ∑ j ∈ range M, monomial j ((-1 : ℚ)^j * ((k+j).choose k : ℚ))
def logTaylor (M : ℕ) : ℚ[X] :=
  ∑ j ∈ range M, monomial j (-(-1 : ℚ)^j/(j : ℚ))
def defectPolynomial (M : ℕ) : ℚ[X] :=
  logTaylor (M+1) + ∑ j ∈ range M,
    C (-_root_.bernoulli (j+1)/(j+1)) * X^(j+1) * (inverseTaylor j (M+1)-1) -
      X * inverseTaylor 0 (M+1)

@[simp] theorem inverseTaylor_coeff (k M r : ℕ) :
    (inverseTaylor k M).coeff r = if r < M then (-1 : ℚ)^r*((k+r).choose k : ℚ) else 0 := by
  simp [inverseTaylor, finsetSum_coeff, coeff_monomial, eq_comm]
@[simp] theorem logTaylor_coeff (M r : ℕ) :
    (logTaylor M).coeff r = if r < M then -(-1 : ℚ)^r/(r : ℚ) else 0 := by
  simp [logTaylor, finsetSum_coeff, coeff_monomial, eq_comm]

theorem defectPolynomial_coeff_zero (M : ℕ) : (defectPolynomial M).coeff 0 = 0 := by
  simp [defectPolynomial, finsetSum_coeff, mul_assoc]

theorem correctionPolynomial_coeff (j r M : ℕ) (hr : r < M) :
    (C (-_root_.bernoulli (j+1)/(j+1)) * X^(j+1) *
      (inverseTaylor j (M+1)-1)).coeff (r+1) =
      if j < r then (-_root_.bernoulli (j+1)/(j+1)) *
        (-1 : ℚ)^(r-j) * (r.choose j : ℚ) else 0 := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  by_cases hj : j ≤ r
  · rw [ite_eq_left (by omega), Nat.add_sub_add_right, coeff_sub,
      inverseTaylor_coeff, ite_eq_left (by omega)]
    by_cases he : j = r
    · subst j
      simp
    · have hjr : j < r := lt_of_le_of_ne hj he
      rw [ite_eq_left hjr, coeff_one, ite_eq_right (by omega), sub_zero,
        Nat.add_sub_of_le hj]
      ring
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]

theorem defectPolynomial_coeff_succ (M r : ℕ) (hr : r < M) :
    (defectPolynomial M).coeff (r+1) = 0 := by
  simp only [defectPolynomial, coeff_sub, coeff_add, finsetSum_coeff,
    logTaylor_coeff, coeff_X_mul, inverseTaylor_coeff]
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  simp only [Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, mul_one]
  simp_rw [correctionPolynomial_coeff _ _ _ hr]
  have hs : (∑ j ∈ range M, if j < r then (-_root_.bernoulli (j+1)/(j+1)) *
      (-1 : ℚ)^(r-j) * (r.choose j : ℚ) else 0) =
      ∑ j ∈ range r, (-_root_.bernoulli (j+1)/(j+1)) *
        (-1 : ℚ)^(r-j) * (r.choose j : ℚ) := by
    rw [← sum_filter]
    congr 1
    ext j
    simp only [mem_filter, mem_range]
    omega
  rw [hs]
  have h := bernoulli_defect_cancellation r
  have hp : -(-1 : ℚ)^(r+1) = (-1 : ℚ)^(r+2) := by ring
  rw [hp]
  norm_num only [Nat.cast_add, Nat.cast_one]
  linear_combination h

theorem defectPolynomial_divisible (M : ℕ) : X^(M+1) ∣ defectPolynomial M := by
  apply X_pow_dvd_iff.mpr
  intro r hr
  cases r with
  | zero => exact defectPolynomial_coeff_zero M
  | succ r => exact defectPolynomial_coeff_succ M r (by omega)

end CircleKernel
