import Mathlib.NumberTheory.BernoulliPolynomials

noncomputable section
open Finset
namespace CircleKernel

theorem bernoulli_signed_sum (r : ℕ) :
    ∑ k ∈ range r, bernoulli k * (r.choose k : ℚ) * (-1 : ℚ)^(r-k) =
      -(r : ℚ) * (-1 : ℚ)^(r-1) := by
  have h := Polynomial.bernoulli_eval_one_add r (-1)
  simp only [add_neg_cancel, Polynomial.bernoulli_eval_zero] at h
  rw [Polynomial.bernoulli, Polynomial.eval_finsetSum, sum_range_succ] at h
  simp only [Polynomial.eval_monomial, Nat.choose_self, Nat.sub_self, pow_zero,
    mul_one] at h
  norm_num only [Nat.cast_one] at h
  linear_combination -h

theorem bernoulli_defect_cancellation (n : ℕ) :
    (-1 : ℚ)^(n+2)/(n+1) +
      ∑ j ∈ range n, (-bernoulli (j+1)/(j+1)) *
        (-1 : ℚ)^(n-j) * (n.choose j : ℚ) = (-1 : ℚ)^n := by
  have h := bernoulli_signed_sum (n+1)
  rw [sum_range_succ'] at h
  simp only [bernoulli_zero, Nat.choose_zero_right, Nat.sub_zero, one_mul,
    Nat.add_sub_add_right, Nat.add_sub_cancel] at h
  have hs : (n+1 : ℚ) * (∑ j ∈ range n, (-bernoulli (j+1)/(j+1)) *
        (-1 : ℚ)^(n-j) * (n.choose j : ℚ)) =
      -(∑ j ∈ range n, bernoulli (j+1) * ((n+1).choose (j+1) : ℚ) *
        (-1 : ℚ)^(n-j)) := by
    rw [mul_sum, ← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    have hc : (n+1 : ℚ) * (n.choose j : ℚ) =
        ((n+1).choose (j+1) : ℚ) * (j+1 : ℚ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n j
    have hj0 : (j+1 : ℚ) ≠ 0 := by positivity
    field_simp
    linear_combination -bernoulli (j+1) * hc
  have hn0 : (n+1 : ℚ) ≠ 0 := by positivity
  apply (mul_left_cancel₀ hn0)
  rw [mul_add, mul_div_cancel₀ _ hn0, hs]
  simp only [pow_succ, Nat.cast_add, Nat.cast_one] at h ⊢
  linear_combination -h

end CircleKernel
