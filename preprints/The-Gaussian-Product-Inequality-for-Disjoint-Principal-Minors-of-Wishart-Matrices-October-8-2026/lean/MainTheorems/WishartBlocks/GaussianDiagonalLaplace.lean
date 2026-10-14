import MainTheorems.WishartBlocks.GaussianQuadratic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Pi

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

theorem gaussian_quadratic_integral_normalized (μ : ℝ) {v : ℝ≥0}
    (hv : v ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    ∫ x : ℝ, Real.exp (-(t * x ^ 2)) ∂(gaussianReal μ v) =
      (Real.sqrt (1 + 2 * (v : ℝ) * t))⁻¹ *
        Real.exp (-(t * μ ^ 2) / (1 + 2 * (v : ℝ) * t)) := by
  rw [gaussian_quadratic_integral μ hv ht]
  have hv' : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hC : Real.sqrt (2 * Real.pi * (v : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [← mul_div_assoc, Real.sqrt_div (by positivity)]
  field_simp

theorem gaussian_shifted_quadratic_integral (m : ℝ) {v : ℝ≥0}
    (hv : v ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    ∫ x : ℝ, Real.exp (-(t * (x + m) ^ 2)) ∂(gaussianReal 0 v) =
      (Real.sqrt (1 + 2 * (v : ℝ) * t))⁻¹ *
        Real.exp (-(t * m ^ 2) / (1 + 2 * (v : ℝ) * t)) := by
  have hm : (gaussianReal 0 v).map (fun x => x + m) = gaussianReal m v := by
    simpa only [zero_add] using gaussianReal_map_add_const m (μ := (0 : ℝ)) (v := v)
  have h := gaussian_quadratic_integral_normalized m hv ht
  rw [← hm, integral_map (by fun_prop) (by fun_prop)] at h
  exact h

theorem gaussian_diagonal_laplace {ι : Type*} [Fintype ι]
    (m t : ι → ℝ) (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) (ht : ∀ i, 0 ≤ t i) :
    ∫ x : ι → ℝ, Real.exp (-(∑ i, t i * (x i + m i) ^ 2))
        ∂(Measure.pi fun i => gaussianReal 0 (v i)) =
      (∏ i, (Real.sqrt (1 + 2 * (v i : ℝ) * t i))⁻¹) *
        Real.exp (-(∑ i, (t i * m i ^ 2) / (1 + 2 * (v i : ℝ) * t i))) := by
  classical
  simp_rw [← Finset.sum_neg_distrib, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod
    (f := fun i x => Real.exp (-(t i * (x + m i) ^ 2)))]
  simp_rw [gaussian_shifted_quadratic_integral _ (hv _) (ht _)]
  rw [Finset.prod_mul_distrib]
  simp only [neg_div]

theorem stdGaussian_diagonal_laplace {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (b : OrthonormalBasis ι ℝ E) (m t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    ∫ y : E, Real.exp (-(∑ i, t i * (b.repr y i + m i) ^ 2)) ∂(stdGaussian E) =
      (∏ i, (Real.sqrt (1 + 2 * t i))⁻¹) *
        Real.exp (-(∑ i, (t i * m i ^ 2) / (1 + 2 * t i))) := by
  classical
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,
    integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  have he : ∀ x : ι → ℝ, b.repr (∑ i, x i • b i) = WithLp.toLp 2 x := by
    intro x
    change b.repr (∑ i, (WithLp.toLp 2 x) i • b i) = _
    rw [b.sum_repr_symm, b.repr.apply_symm_apply]
  simp only [he, PiLp.toLp_apply]
  simpa only [NNReal.coe_one, mul_one] using
    gaussian_diagonal_laplace m t (fun _ => 1) (by simp) ht

end ResearchMain.WishartBlocks
