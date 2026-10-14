import MainTheorems.Corona.BaseGraphs
import Mathlib.Algebra.Polynomial.Roots

namespace ResearchMain.Corona

open Classical Polynomial

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem independencePolynomial_eval_ge_one (H : SimpleGraph W) {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ (independencePolynomial H).eval x := by
  have hm : (∅ : Finset W) ∈ independentSets H :=
    (mem_independentSets _ _).mpr (independent_empty H)
  have h := Finset.single_le_sum (s := independentSets H)
    (f := fun S => x ^ S.card) (fun _ _ => pow_nonneg hx _) hm
  simp only [Finset.card_empty, pow_zero] at h
  rw [independencePolynomial, eval_finsetSum]
  simp only [eval_pow, eval_X]
  exact h

theorem independencePolynomial_eval_positive (H : SimpleGraph W) {x : ℝ} (hx : 0 ≤ x) :
    0 < (independencePolynomial H).eval x := lt_of_lt_of_le zero_lt_one
  (independencePolynomial_eval_ge_one H hx)

theorem scaled_monomial {q x : ℝ} (hq : q ≠ 0) {N j : ℕ} (hj : j ≤ N) :
    q ^ N * (x / q) ^ j = x ^ j * q ^ (N - j) := by
  calc
    _ = q ^ (N - j) * q ^ j * (x ^ j / q ^ j) := by
      rw [← pow_add, Nat.sub_add_cancel hj, div_pow]
    _ = _ := by field_simp

theorem independencePolynomial_corona_eval (G : SimpleGraph V) (H : SimpleGraph W)
    {x : ℝ} (hH : (independencePolynomial H).eval x ≠ 0) :
    (independencePolynomial (corona G H)).eval x =
      (independencePolynomial H).eval x ^ Fintype.card V *
        (independencePolynomial G).eval (x / (independencePolynomial H).eval x) := by
  rw [independencePolynomial_corona, eval_finsetSum]
  simp only [eval_mul, eval_pow, eval_X]
  have hG : (independencePolynomial G).eval (x / (independencePolynomial H).eval x) =
      ∑ S ∈ independentSets G, (x / (independencePolynomial H).eval x) ^ S.card := by
    simp only [independencePolynomial, eval_finsetSum, eval_pow, eval_X]
  rw [hG, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  exact (scaled_monomial hH (Finset.card_le_univ S)).symm

theorem scaled_binomial {q x : ℝ} (hq : q ≠ 0) {N j : ℕ} (hj : j ≤ N) :
    q ^ N * (1 + x / q) ^ j = q ^ (N - j) * (q + x) ^ j := by
  have he : 1 + x / q = (q + x) / q := by field_simp
  rw [he, scaled_monomial hq hj]
  ring

noncomputable def twoPeakPolynomial (h : ℝ[X]) (a m : ℕ) : ℝ[X] :=
  h ^ (2 * m) * (h + X) ^ a + h ^ (a + m) * (h + C 2 * X) ^ m - h ^ (a + 2 * m)

theorem independencePolynomial_corona_baseGraph (H : SimpleGraph W) (a m : ℕ) :
    independencePolynomial (corona (baseGraph a m) H) =
      twoPeakPolynomial (independencePolynomial H) a m := by
  apply eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (0 : ℝ)).mono
  intro x hx
  change (independencePolynomial (corona (baseGraph a m) H)).eval x =
    (twoPeakPolynomial (independencePolynomial H) a m).eval x
  have hq : (independencePolynomial H).eval x ≠ 0 :=
    ne_of_gt (independencePolynomial_eval_positive H (le_of_lt hx))
  rw [independencePolynomial_corona_eval _ _ hq, baseGraph_order,
    independencePolynomial_baseGraph]
  simp only [eval_sub, eval_add, eval_pow, eval_one, eval_mul, eval_C, eval_X, mul_sub, mul_add, mul_one]
  rw [scaled_binomial hq (show a ≤ a + 2 * m by omega)]
  have he : (1 + 2 * (x / (independencePolynomial H).eval x)) =
      1 + (2 * x) / (independencePolynomial H).eval x := by ring
  rw [he, scaled_binomial hq (show m ≤ a + 2 * m by omega)]
  simp only [show a + 2 * m - a = 2 * m by omega,
    show a + 2 * m - m = a + m by omega]
  simp only [twoPeakPolynomial, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]

end ResearchMain.Corona
