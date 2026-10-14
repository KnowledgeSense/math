import MainTheorems.Corona.Rescaling

namespace ResearchMain.Corona

open Polynomial

theorem homogeneous_product (t q x : ℝ) (p r : ℕ) :
    (t * q) ^ p * (t * q + t * x) ^ r = t ^ (p + r) * (q ^ p * (q + x) ^ r) := by
  rw [show t * q + t * x = t * (q + x) by ring, mul_pow, mul_pow, pow_add]
  ring

theorem twoPeak_comp (h : ℝ[X]) {t : ℝ} (ht : t ≠ 0) (a m : ℕ) :
    (twoPeakPolynomial h a m).comp (C t * X) =
      C (t ^ (a + 2 * m)) * twoPeakPolynomial (rescale h t) a m := by
  apply Polynomial.funext
  intro x
  have he : h.eval (t * x) = t * (rescale h t).eval x := by
    rw [rescale_eval]
    symm
    calc
      _ = (t * t⁻¹) * h.eval (t * x) := by ring
      _ = _ := by rw [mul_inv_cancel₀ ht, one_mul]
  rw [eval_comp]
  simp only [twoPeakPolynomial, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  rw [he, show 2 * (t * x) = t * (2 * x) by ring,
    homogeneous_product, homogeneous_product, mul_pow]
  rw [show 2 * m + a = a + 2 * m by omega, show a + m + m = a + 2 * m by omega]
  ring

theorem corona_baseGraph_comp {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    {t : ℝ} (ht : t ≠ 0) (a m : ℕ) :
    (independencePolynomial (corona (baseGraph a m) H)).comp (C t * X) =
      C (t ^ (a + 2 * m)) * twoPeakPolynomial (rescale (independencePolynomial H) t) a m := by
  rw [independencePolynomial_corona_baseGraph, twoPeak_comp _ ht]

end ResearchMain.Corona
