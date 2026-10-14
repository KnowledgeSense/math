import MainTheorems.WishartBlocks.MatrixGaussianLaplace

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace NNReal ENNReal

theorem gaussian_linear_quadratic_integral {v : ℝ≥0} (hv : v ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) (u : ℝ) :
    ∫ x : ℝ, Real.exp (-(t * x ^ 2) + u * x) ∂(gaussianReal 0 v) =
      (Real.sqrt (1 + 2 * (v : ℝ) * t))⁻¹ *
        Real.exp (((v : ℝ) * u ^ 2) / (2 * (1 + 2 * (v : ℝ) * t))) := by
  have hv' : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hD : 0 < 1 + 2 * (v : ℝ) * t := by positivity
  have hex : ∀ x : ℝ, -(x ^ 2) / (2 * (v : ℝ)) + (-(t * x ^ 2) + u * x) =
      (v : ℝ) * u ^ 2 / 2 +
        (-(x - (v : ℝ) * u) ^ 2 / (2 * (v : ℝ)) + -(t * x ^ 2)) := by
    intro x
    field_simp
    ring
  have he : ∀ x : ℝ, gaussianPDFReal 0 v x * Real.exp (-(t * x ^ 2) + u * x) =
      Real.exp ((v : ℝ) * u ^ 2 / 2) *
        (gaussianPDFReal ((v : ℝ) * u) v x * Real.exp (-(t * x ^ 2))) := by
    intro x
    unfold gaussianPDFReal
    simp only [sub_zero]
    calc
      (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x ^ 2) / (2 * (v : ℝ))) *
          Real.exp (-(t * x ^ 2) + u * x) =
        (Real.sqrt (2 * Real.pi * v))⁻¹ *
          Real.exp (-(x ^ 2) / (2 * (v : ℝ)) + (-(t * x ^ 2) + u * x)) := by
            rw [mul_assoc, ← Real.exp_add]
      _ = (Real.sqrt (2 * Real.pi * v))⁻¹ *
          (Real.exp ((v : ℝ) * u ^ 2 / 2) *
            Real.exp (-(x - (v : ℝ) * u) ^ 2 / (2 * (v : ℝ)) + -(t * x ^ 2))) := by
              rw [hex, Real.exp_add]
      _ = _ := by rw [Real.exp_add]; ring
  have hmean := gaussian_quadratic_integral_normalized ((v : ℝ) * u) hv ht
  rw [integral_gaussianReal_eq_integral_smul hv] at hmean ⊢
  simp only [smul_eq_mul] at hmean ⊢
  rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_const_mul, hmean]
  have heD : (v : ℝ) * u ^ 2 / 2 +
      -(t * ((v : ℝ) * u) ^ 2) / (1 + 2 * (v : ℝ) * t) =
      ((v : ℝ) * u ^ 2) / (2 * (1 + 2 * (v : ℝ) * t)) := by
    field_simp
    ring
  calc
    _ = (Real.sqrt (1 + 2 * (v : ℝ) * t))⁻¹ *
        Real.exp ((v : ℝ) * u ^ 2 / 2 +
          -(t * ((v : ℝ) * u) ^ 2) / (1 + 2 * (v : ℝ) * t)) := by
            rw [Real.exp_add]
            ring
    _ = _ := by rw [heD]

theorem gaussian_linear_diagonal_laplace {ι : Type*} [Fintype ι]
    (u t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    ∫ x : ι → ℝ, Real.exp (∑ i, (-(t i * x i ^ 2) + u i * x i))
        ∂(Measure.pi fun _ => gaussianReal 0 1) =
      (∏ i, (Real.sqrt (1 + 2 * t i))⁻¹) *
        Real.exp (∑ i, (u i ^ 2) / (2 * (1 + 2 * t i))) := by
  classical
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod
    (f := fun i x => Real.exp (-(t i * x ^ 2) + u i * x))]
  simp_rw [gaussian_linear_quadratic_integral (by simp : (1 : ℝ≥0) ≠ 0) (ht _) (u _)]
  simp only [NNReal.coe_one, one_mul, mul_one]
  rw [Finset.prod_mul_distrib]

theorem matrix_inverse_resolvent_quadratic {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (u : EuclideanSpace ℝ (Fin n)) :
    ⟪u, ((1 + c • A)⁻¹).toEuclideanLin u⟫_ℝ =
      ∑ i, (hA.1.eigenvectorBasis.repr u i) ^ 2 / (1 + c * hA.1.eigenvalues i) := by
  rw [quadratic_in_orthonormalBasis hA.1.eigenvectorBasis _ _
    (matrix_one_add_smul_inverse_eigenvector hA hc) u]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem matrix_gaussian_linear_laplace {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (u : EuclideanSpace ℝ (Fin n)) :
    ∫ z : EuclideanSpace ℝ (Fin n),
        Real.exp (-⟪z, A.toEuclideanLin z⟫_ℝ + ⟪u, z⟫_ℝ)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
      (Real.sqrt ((1 + (2 : ℝ) • A).det))⁻¹ *
        Real.exp (⟪u, ((1 + (2 : ℝ) • A)⁻¹).toEuclideanLin u⟫_ℝ / 2) := by
  classical
  let b := hA.1.eigenvectorBasis
  have hi : ∀ z : EuclideanSpace ℝ (Fin n),
      ⟪u, z⟫_ℝ = ∑ i, b.repr u i * b.repr z i := by
    intro z
    rw [← b.repr.inner_map_map u z, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.inner_apply, mul_comm]
  have he : ∀ z : EuclideanSpace ℝ (Fin n),
      -⟪z, A.toEuclideanLin z⟫_ℝ + ⟪u, z⟫_ℝ =
        ∑ i, (-(hA.1.eigenvalues i * b.repr z i ^ 2) + b.repr u i * b.repr z i) := by
    intro z
    rw [matrix_quadratic_eigenbasis hA.1, hi, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
  simp_rw [he]
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,
    integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  simp only [orthonormalBasis_repr_sum, PiLp.toLp_apply]
  rw [gaussian_linear_diagonal_laplace _ _ hA.eigenvalues_nonneg,
    matrix_inverse_resolvent_quadratic hA (by norm_num : (0 : ℝ) ≤ 2),
    matrix_one_add_smul_det hA.1, Real.sqrt_prod,
    Finset.prod_inv_distrib, Finset.sum_div]
  · congr 2
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [b]
    have hEig := hA.eigenvalues_nonneg i
    have hD : 1 + 2 * hA.1.eigenvalues i ≠ 0 := by positivity
    field_simp [hD]
  · intro i _
    have hEig := hA.eigenvalues_nonneg i
    positivity

end ResearchMain.WishartBlocks

