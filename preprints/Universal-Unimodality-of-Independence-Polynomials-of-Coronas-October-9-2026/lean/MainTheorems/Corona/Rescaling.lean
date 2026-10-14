import MainTheorems.Corona.DerivativeCounting
import MainTheorems.Corona.PeakParameters

namespace ResearchMain.Corona

open Polynomial

noncomputable def rescale (h : ℝ[X]) (t : ℝ) : ℝ[X] := C t⁻¹ * h.comp (C t * X)

theorem rescale_coeff (h : ℝ[X]) (t : ℝ) (k : ℕ) :
    (rescale h t).coeff k = t⁻¹ * h.coeff k * t ^ k := by
  rw [rescale, coeff_C_mul, comp_C_mul_X_coeff]
  ring

theorem rescale_eval (h : ℝ[X]) (t x : ℝ) : (rescale h t).eval x = t⁻¹ * h.eval (t * x) := by
  simp only [rescale, eval_mul, eval_C, eval_comp, eval_X]

theorem rescale_mass (h : ℝ[X]) (t : ℝ) : mass (rescale h t) = h.eval t / t := by
  rw [mass, rescale_eval, mul_one]
  ring

theorem rescale_firstMoment (h : ℝ[X]) {t : ℝ} (ht : t ≠ 0) :
    firstMoment (rescale h t) = h.derivative.eval t := by
  simp only [firstMoment, eulerDerivative, rescale, derivative_mul, derivative_C, zero_mul,
    zero_add, derivative_comp, derivative_X, mul_one, eval_mul, eval_C, eval_X, eval_comp]
  field_simp

theorem rescale_mean (h : ℝ[X]) {t : ℝ} (ht : t ≠ 0) (hh : h.eval t ≠ 0) :
    mean (rescale h t) = t * h.derivative.eval t / h.eval t := by
  rw [mean, rescale_firstMoment _ ht, rescale_mass]
  field_simp

theorem rescale_nonnegative {h : ℝ[X]} (hh : NonnegativeCoefficients h) {t : ℝ} (ht : 0 ≤ t) :
    NonnegativeCoefficients (rescale h t) := by
  intro k
  rw [rescale_coeff]
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr ht) (hh k)) (pow_nonneg ht k)

theorem rescale_graph_mass {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : 1 ≤ mass (rescale (independencePolynomial H) t) := by
  rw [rescale_mass]
  apply (le_div_iff₀ ht).mpr
  have hh := independencePolynomial_eval_ge_one H ht.le
  simpa only [one_mul] using ht1.trans hh

theorem rescale_graph_mean_lt_one {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) :
    mean (rescale (independencePolynomial H) (1 / ((Fintype.card W : ℝ) + 1))) < 1 := by
  let t : ℝ := 1 / ((Fintype.card W : ℝ) + 1)
  have ht : 0 < t := by dsimp only [t]; positivity
  have hh := independencePolynomial_eval_positive H ht.le
  rw [rescale_mean _ (ne_of_gt ht) (ne_of_gt hh)]
  have hbound := mul_le_mul_of_nonneg_left (independencePolynomial_derivative_bound H ht.le) ht.le
  have hratio : t * (independencePolynomial H).derivative.eval t /
      (independencePolynomial H).eval t ≤ t * Fintype.card W := by
    apply (div_le_iff₀ hh).mpr
    nlinarith only [hbound]
  apply hratio.trans_lt
  dsimp only [t]
  have hr0 : (0 : ℝ) ≤ Fintype.card W := by positivity
  have he : 1 / ((Fintype.card W : ℝ) + 1) * Fintype.card W =
      (Fintype.card W : ℝ) / (Fintype.card W + 1) := by ring
  rw [he]
  exact (div_lt_one (by linarith)).mpr (by linarith)

end ResearchMain.Corona
