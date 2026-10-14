import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace Fan

/-- The elementary binomial kernel, with its full finite support. -/
def delannoy (z : ℝ) (a b : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (min a b + 1), (a.choose k : ℝ) * b.choose k * z^k

/-- The polynomial whose evaluation is the elementary binomial kernel. -/
def delannoyPolynomial (a b : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (min a b + 1), Polynomial.monomial k ((a.choose k : ℝ) * b.choose k)

theorem delannoyPolynomial_eval (z : ℝ) (a b : ℕ) :
    (delannoyPolynomial a b).eval z = delannoy z a b := by
  simp [delannoyPolynomial, delannoy, Polynomial.eval_finsetSum]

theorem delannoy_symm (z : ℝ) (a b : ℕ) : delannoy z a b = delannoy z b a := by
  unfold delannoy
  rw [min_comm]
  apply Finset.sum_congr rfl
  intro k _
  ring

@[simp] theorem delannoy_zero_left (z : ℝ) (b : ℕ) : delannoy z 0 b = 1 := by
  simp [delannoy]

@[simp] theorem delannoy_zero_right (z : ℝ) (a : ℕ) : delannoy z a 0 = 1 := by
  rw [delannoy_symm, delannoy_zero_left]

theorem delannoy_ge_one {z : ℝ} (hz : 0 ≤ z) (a b : ℕ) : 1 ≤ delannoy z a b := by
  have h := Finset.single_le_sum (f := fun k => (a.choose k : ℝ) * b.choose k * z^k)
    (s := Finset.range (min a b + 1)) (a := 0)
    (fun k _ => by positivity) (by simp)
  simpa [delannoy] using h

theorem delannoy_pos {z : ℝ} (hz : 0 ≤ z) (a b : ℕ) : 0 < delannoy z a b :=
  lt_of_lt_of_le zero_lt_one (delannoy_ge_one hz a b)

theorem delannoyPolynomial_coeff (a b k : ℕ) :
    (delannoyPolynomial a b).coeff k = (a.choose k : ℝ) * b.choose k := by
  unfold delannoyPolynomial
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hk : k < min a b + 1
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [hj]
    · simp [hk]
  · have he : a < k ∨ b < k := by omega
    have hc : (a.choose k : ℝ) * b.choose k = 0 := by
      rcases he with he | he <;> simp [Nat.choose_eq_zero_of_lt he]
    rw [hc]
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : k ≠ j := by have := Finset.mem_range.mp hj; omega
    simp [Ne.symm hjk]

@[simp] theorem delannoyPolynomial_constant (a b : ℕ) :
    (delannoyPolynomial a b).coeff 0 = 1 := by simp [delannoyPolynomial_coeff]

theorem delannoyPolynomial_ne_zero (a b : ℕ) : delannoyPolynomial a b ≠ 0 := by
  intro h
  have := delannoyPolynomial_constant a b
  simp [h] at this

end Fan
