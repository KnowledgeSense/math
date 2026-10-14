import MainTheorems.WishartBlocks.GaussianDiagonalLaplace
import Mathlib.Analysis.Matrix.PosDef

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

theorem orthonormalBasis_repr_sum {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E) (x : ι → ℝ) :
    b.repr (∑ i, x i • b i) = WithLp.toLp 2 x := by
  change b.repr (∑ i, (WithLp.toLp 2 x) i • b i) = _
  rw [b.sum_repr_symm, b.repr.apply_symm_apply]

theorem quadratic_in_orthonormalBasis {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E) (L : E →ₗ[ℝ] E) (a : ι → ℝ)
    (hL : ∀ i, L (b i) = a i • b i) (y : E) :
    ⟪y, L y⟫_ℝ = ∑ i, a i * (b.repr y i) ^ 2 := by
  have he : L y = ∑ i, (b.repr y i * a i) • b i := by
    nth_rw 1 [← b.sum_repr y]
    rw [map_sum]
    simp_rw [map_smul, hL, smul_smul]
  rw [← b.repr.inner_map_map y (L y), he, orthonormalBasis_repr_sum, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Real.inner_apply]
  ring

theorem matrix_eigenvector_action {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (i : Fin n) :
    A.toEuclideanLin (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
  ext j
  exact congrFun (hA.mulVec_eigenvectorBasis i) j

theorem matrix_one_add_smul_eigenvector {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (c : ℝ) (i : Fin n) :
    (1 + c • A).toEuclideanLin (hA.eigenvectorBasis i) =
      (1 + c * hA.eigenvalues i) • hA.eigenvectorBasis i := by
  rw [map_add, map_smul, Matrix.toLpLin_one]
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
    matrix_eigenvector_action hA, smul_smul, add_smul, one_smul]

theorem linearMap_toMatrix_eigenbasis {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E) (L : E →ₗ[ℝ] E) (a : ι → ℝ)
    (hL : ∀ i, L (b i) = a i • b i) :
    LinearMap.toMatrix b.toBasis b.toBasis L = Matrix.diagonal a := by
  ext i j
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, hL,
    map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

theorem matrix_one_add_smul_det {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (c : ℝ) :
    (1 + c • A).det = ∏ i, (1 + c * hA.eigenvalues i) := by
  have he := linearMap_toMatrix_eigenbasis hA.eigenvectorBasis
    (1 + c • A).toEuclideanLin (fun i => 1 + c * hA.eigenvalues i)
    (matrix_one_add_smul_eigenvector hA c)
  have hd := congrArg Matrix.det he
  rw [LinearMap.det_toMatrix, LinearMap.det_toLpLin, Matrix.det_diagonal] at hd
  exact hd

theorem matrix_one_add_smul_inverse_eigenvector {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (i : Fin n) :
    ((1 + c • A)⁻¹).toEuclideanLin (hA.1.eigenvectorBasis i) =
      (1 + c * hA.1.eigenvalues i)⁻¹ • hA.1.eigenvectorBasis i := by
  have hD : ∀ j, 0 < 1 + c * hA.1.eigenvalues j := fun j => by
    have hEig := hA.eigenvalues_nonneg j
    positivity
  have hdet : IsUnit (1 + c • A).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [matrix_one_add_smul_det hA.1]
    exact (Finset.prod_pos fun j _ => hD j).ne'
  have ht : ((1 + c • A)⁻¹).toEuclideanLin
      ((1 + c • A).toEuclideanLin (hA.1.eigenvectorBasis i)) =
      hA.1.eigenvectorBasis i := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      Matrix.nonsing_inv_mul _ hdet, Matrix.toLpLin_one]
    rfl
  rw [matrix_one_add_smul_eigenvector hA.1, map_smul] at ht
  have hi := congrArg (fun y => (1 + c * hA.1.eigenvalues i)⁻¹ • y) ht
  simpa only [inv_smul_smul₀ (hD i).ne'] using hi

theorem matrix_resolvent_quadratic {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) (m : EuclideanSpace ℝ (Fin n)) :
    ⟪m, (A * (1 + c • A)⁻¹).toEuclideanLin m⟫_ℝ =
      ∑ i, (hA.1.eigenvalues i * (hA.1.eigenvectorBasis.repr m i) ^ 2) /
        (1 + c * hA.1.eigenvalues i) := by
  have ha : ∀ i, (A * (1 + c • A)⁻¹).toEuclideanLin (hA.1.eigenvectorBasis i) =
      (hA.1.eigenvalues i / (1 + c * hA.1.eigenvalues i)) •
        hA.1.eigenvectorBasis i := by
    intro i
    rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply,
      matrix_one_add_smul_inverse_eigenvector hA hc, map_smul,
      matrix_eigenvector_action hA.1, smul_smul]
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  rw [quadratic_in_orthonormalBasis hA.1.eigenvectorBasis _ _ ha m]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem matrix_quadratic_eigenbasis {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (y : EuclideanSpace ℝ (Fin n)) :
    ⟪y, A.toEuclideanLin y⟫_ℝ =
      ∑ i, hA.eigenvalues i * (hA.eigenvectorBasis.repr y i) ^ 2 :=
  quadratic_in_orthonormalBasis hA.eigenvectorBasis A.toEuclideanLin
    hA.eigenvalues (matrix_eigenvector_action hA) y

theorem matrix_gaussian_laplace_spectral {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (m : EuclideanSpace ℝ (Fin n)) :
    ∫ z : EuclideanSpace ℝ (Fin n),
        Real.exp (-⟪z + m, A.toEuclideanLin (z + m)⟫_ℝ)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
      (∏ i, (Real.sqrt (1 + 2 * hA.1.eigenvalues i))⁻¹) *
        Real.exp (-(∑ i,
          (hA.1.eigenvalues i * (hA.1.eigenvectorBasis.repr m i) ^ 2) /
            (1 + 2 * hA.1.eigenvalues i))) := by
  simp_rw [matrix_quadratic_eigenbasis hA.1, map_add, PiLp.add_apply]
  exact stdGaussian_diagonal_laplace hA.1.eigenvectorBasis
    (fun i => hA.1.eigenvectorBasis.repr m i) hA.1.eigenvalues hA.eigenvalues_nonneg

theorem matrix_gaussian_laplace {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (m : EuclideanSpace ℝ (Fin n)) :
    ∫ z : EuclideanSpace ℝ (Fin n),
        Real.exp (-⟪z + m, A.toEuclideanLin (z + m)⟫_ℝ)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
      (Real.sqrt ((1 + (2 : ℝ) • A).det))⁻¹ *
        Real.exp (-⟪m, (A * (1 + (2 : ℝ) • A)⁻¹).toEuclideanLin m⟫_ℝ) := by
  rw [matrix_gaussian_laplace_spectral hA,
    matrix_resolvent_quadratic hA (by norm_num : (0 : ℝ) ≤ 2),
    matrix_one_add_smul_det hA.1, Real.sqrt_prod,
    Finset.prod_inv_distrib]
  intro i _
  have hEig := hA.eigenvalues_nonneg i
  positivity

end ResearchMain.WishartBlocks
