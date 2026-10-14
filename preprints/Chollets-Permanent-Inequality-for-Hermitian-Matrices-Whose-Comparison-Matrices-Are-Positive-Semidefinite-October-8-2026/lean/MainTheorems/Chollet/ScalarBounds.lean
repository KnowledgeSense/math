import MainTheorems.Chollet.PolynomialSpecialization
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace ResearchMain.Chollet

theorem geometric_sum_bound (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1 / 2) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), s ^ k ≤ 2 - s ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hm : s ^ n * (2 * s) ≤ s ^ n := by
      have h := mul_le_mul_of_nonneg_left (show 2 * s ≤ 1 by linarith)
        (pow_nonneg hs n)
      simpa using h
    nlinarith

theorem geometric_sum_erase_zero_bound (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1 / 2)
    (n : ℕ) : ∑ k ∈ (Finset.range (n + 1)).erase 0, s ^ k ≤ 1 := by
  have h := geometric_sum_bound s hs hs' n
  have he := Finset.add_sum_erase (Finset.range (n + 1)) (fun k => s ^ k)
    (show 0 ∈ Finset.range (n + 1) by simp)
  simp only [pow_zero] at he
  have hn := pow_nonneg hs n
  linarith

theorem polynomial_real_eval (p : Polynomial ℂ) (s : ℝ) :
    (p.eval (s : ℂ)).re =
      ∑ k ∈ Finset.range (p.natDegree + 1), (p.coeff k).re * s ^ k := by
  rw [Polynomial.eval_eq_sum_range, Complex.re_sum]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

theorem polynomial_real_eval_bound (p : Polynomial ℂ) (s : ℝ)
    (hs : 0 ≤ s) (hs' : s ≤ 1 / 2) (h₁ : 0 ≤ (p.coeff 1).re)
    (hc : ∀ k, 0 < k → (p.coeff k).re ≤ (p.coeff 1).re) :
    (p.eval (s : ℂ)).re ≤ (p.coeff 0).re + (p.coeff 1).re := by
  rw [polynomial_real_eval]
  rw [← Finset.add_sum_erase (Finset.range (p.natDegree + 1))
    (fun k => (p.coeff k).re * s ^ k) (show 0 ∈ Finset.range (p.natDegree + 1) by simp)]
  simp only [pow_zero, mul_one]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ k ∈ (Finset.range (p.natDegree + 1)).erase 0, (p.coeff 1).re * s ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right
        (hc k (Nat.pos_of_ne_zero (Finset.mem_erase.mp hk).1)) (pow_nonneg hs k)
    _ = (p.coeff 1).re *
        ∑ k ∈ (Finset.range (p.natDegree + 1)).erase 0, s ^ k := by
      rw [Finset.mul_sum]
    _ ≤ (p.coeff 1).re * 1 :=
      mul_le_mul_of_nonneg_left (geometric_sum_erase_zero_bound s hs hs' _) h₁
    _ = (p.coeff 1).re := mul_one _

theorem sqrt_two_offset_bound :
    0 ≤ Real.sqrt 2 - 1 ∧ Real.sqrt 2 - 1 ≤ (1 : ℝ) / 2 := by
  have hs := Real.sqrt_nonneg (2 : ℝ)
  have he := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  constructor <;> nlinarith

end ResearchMain.Chollet
