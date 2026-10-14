import ReciprocalQGamma.OrderedMinors
import ReciprocalQGamma.Bidiagonal
import Mathlib.Algebra.Polynomial.BigOperators

noncomputable section
open scoped BigOperators
open Polynomial
namespace ReciprocalQGamma

def nestedPolynomial (c : ℕ → ℝ) (k : ℕ) : ℝ[X] :=
  ∏ j ∈ Finset.range k, (X + C (c j))

def intermediatePolynomial (c : ℕ → ℝ) (j k : ℕ) : ℝ[X] :=
  X ^ (k - min k j) * nestedPolynomial c (min k j)

def coefficientMatrix (c : ℕ → ℝ) (m j : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun k d => (intermediatePolynomial c j k.val).coeff d.val

theorem nestedPolynomial_succ (c : ℕ → ℝ) (k : ℕ) :
    nestedPolynomial c (k + 1) = nestedPolynomial c k * (X + C (c k)) := by
  simp [nestedPolynomial, Finset.prod_range_succ]

theorem intermediatePolynomial_stable (c : ℕ → ℝ) (j k : ℕ) (hk : k ≤ j) :
    intermediatePolynomial c (j + 1) k = intermediatePolynomial c j k := by
  simp [intermediatePolynomial, min_eq_left hk, min_eq_left (by omega : k ≤ j + 1)]

theorem intermediatePolynomial_step (c : ℕ → ℝ) (j k : ℕ) (hk : j < k) :
    intermediatePolynomial c (j + 1) k = intermediatePolynomial c j k +
      C (c j) * intermediatePolynomial c j (k - 1) := by
  have h1 : j + 1 ≤ k := by omega
  have h2 : j ≤ k - 1 := by omega
  simp only [intermediatePolynomial, min_eq_right h1, min_eq_right (le_of_lt hk),
    min_eq_right h2, nestedPolynomial_succ]
  have he : k - j = (k - (j + 1)) + 1 := by omega
  have he' : k - 1 - j = k - (j + 1) := by omega
  rw [he, he', pow_succ]
  ring

theorem coefficientMatrix_zero (c : ℕ → ℝ) (m : ℕ) : coefficientMatrix c m 0 = 1 := by
  ext k d
  simp [coefficientMatrix, intermediatePolynomial, nestedPolynomial, Matrix.one_apply,
    eq_comm, Fin.ext_iff]

theorem coefficientMatrix_step (c : ℕ → ℝ) (m j : ℕ) :
    coefficientMatrix c m (j + 1) = lowerBidiagonal m j (c j) * coefficientMatrix c m j := by
  ext k d
  by_cases hk : k.val ≤ j
  · have hn : ¬ j < k.val := by omega
    simp [Matrix.mul_apply, lowerBidiagonal, hn, coefficientMatrix,
      intermediatePolynomial_stable c j k.val hk]
  · have hkj : j < k.val := by omega
    let p : Fin m := ⟨k.val - 1, by omega⟩
    have hpk : p ≠ k := by intro h; have := congrArg Fin.val h; dsimp [p] at this; omega
    have he : ∀ l : Fin m, lowerBidiagonal m j (c j) k l =
        (if l = k then 1 else 0) + (if l = p then c j else 0) := by
      intro l
      unfold lowerBidiagonal
      by_cases hlk : l = k
      · subst l; simp [hpk.symm]
      · have hkl : k ≠ l := Ne.symm hlk
        have hp : l.val + 1 = k.val ↔ l = p := by
          constructor
          · intro h; apply Fin.ext; dsimp [p]; omega
          · intro h; subst l; dsimp [p]; omega
        simp [hkl, hlk, hkj, hp]
    simp_rw [Matrix.mul_apply, he, add_mul, Finset.sum_add_distrib]
    simp only [ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    change (intermediatePolynomial c (j + 1) k.val).coeff d.val = _
    rw [intermediatePolynomial_step c j k.val hkj, Polynomial.coeff_add, Polynomial.coeff_C_mul]
    rfl

theorem coefficientMatrix_totallyNonneg (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j) (m j : ℕ) :
    (coefficientMatrix c m j).IsTotallyNonneg := by
  induction j with
  | zero => rw [coefficientMatrix_zero]; exact Matrix.IsTotallyNonneg.one
  | succ j ih =>
    rw [coefficientMatrix_step]
    exact totallyNonneg_mul _ _ (lowerBidiagonal_totallyNonneg m j (c j) (hc j)) ih

end ReciprocalQGamma
