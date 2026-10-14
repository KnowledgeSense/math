import MainTheorems.WishartBlocks.WishartCongruence
import MainTheorems.WishartBlocks.GaussianLinearLaplace

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder InnerProductSpace

theorem quadratic_matrix_congruence {p : ℕ} (C D : Matrix (Fin p) (Fin p) ℝ)
    (x : EuclideanSpace ℝ (Fin p)) :
    ⟪C.toEuclideanLin x, D.toEuclideanLin (C.toEuclideanLin x)⟫_ℝ =
      ⟪x, (C.transpose * D * C).toEuclideanLin x⟫_ℝ := by
  rw [← euclidean_dotProduct_matrix, ← euclidean_dotProduct_matrix]
  change (C *ᵥ fun i => x i) ⬝ᵥ (D *ᵥ (C *ᵥ fun i => x i)) =
    (fun i => x i) ⬝ᵥ ((C.transpose * D * C) *ᵥ fun i => x i)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

theorem positive_sqrt_isUnit_det {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) : IsUnit (CFC.sqrt S).det := by
  apply isUnit_iff_ne_zero.mpr
  rw [hS.posSemidef.det_sqrt, RCLike.sqrt_real]
  exact (Real.sqrt_pos.mpr hS.det_pos).ne'

theorem sqrt_precision_inverse {p : ℕ} {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosSemidef) :
    (1 + (2 : ℝ) • (S * T))⁻¹ =
      CFC.sqrt S * (1 + (2 : ℝ) •
        ((CFC.sqrt S).transpose * T * CFC.sqrt S))⁻¹ * (CFC.sqrt S)⁻¹ := by
  let R := CFC.sqrt S
  let A := R.transpose * T * R
  let N := 1 + (2 : ℝ) • A
  let M := 1 + (2 : ℝ) • (S * T)
  have hR := positive_sqrt_isUnit_det hS
  have hRt : R.transpose = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg S).posSemidef.1.eq
  have hSq : R * R = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hA : A.PosSemidef := by
    simpa only [A, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hT.conjTranspose_mul_mul_same R
  have hNpos : 0 < N.det := by
    rw [matrix_one_add_smul_det hA.1]
    apply Finset.prod_pos
    intro i _
    have hEig := hA.eigenvalues_nonneg i
    positivity
  have hN : IsUnit N.det := isUnit_iff_ne_zero.mpr hNpos.ne'
  have hM : IsUnit M.det := by
    have he : N.det = M.det := sqrt_congruence_precision_det hS.posSemidef T
    rwa [← he]
  have hpush : M * R = R * N := by
    dsimp [M, N, A]
    rw [hRt]
    rw [← hSq]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hp : M⁻¹ * R = R * N⁻¹ := by
    calc
      _ = (M⁻¹ * R) * (N * N⁻¹) := by rw [Matrix.mul_nonsing_inv _ hN, Matrix.mul_one]
      _ = M⁻¹ * (R * N) * N⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ * (M * R) * N⁻¹ := by rw [← hpush]
      _ = _ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]
  calc
    _ = (M⁻¹ * R) * R⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hR,
      Matrix.mul_one]
    _ = _ := by rw [hp]

theorem sqrt_precision_resolvent {p : ℕ} {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosSemidef) :
    ((CFC.sqrt S)⁻¹).transpose *
        (((CFC.sqrt S).transpose * T * CFC.sqrt S) *
          (1 + (2 : ℝ) • ((CFC.sqrt S).transpose * T * CFC.sqrt S))⁻¹) *
        (CFC.sqrt S)⁻¹ = T * (1 + (2 : ℝ) • (S * T))⁻¹ := by
  have hR := positive_sqrt_isUnit_det hS
  have hRt : (CFC.sqrt S).transpose = CFC.sqrt S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg S).posSemidef.1.eq
  rw [Matrix.transpose_nonsing_inv, hRt, sqrt_precision_inverse hS hT]
  simp only [hRt]
  calc
    _ = ((CFC.sqrt S)⁻¹ * CFC.sqrt S) * T *
        (CFC.sqrt S * (1 + (2 : ℝ) • (CFC.sqrt S * T * CFC.sqrt S))⁻¹ *
          (CFC.sqrt S)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.nonsing_inv_mul _ hR, Matrix.one_mul]

theorem gaussian_affine_laplace {p : ℕ} {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosSemidef) (m : EuclideanSpace ℝ (Fin p)) :
    ∫ z : EuclideanSpace ℝ (Fin p),
        Real.exp (-⟪(CFC.sqrt S).toEuclideanLin z + m,
          T.toEuclideanLin ((CFC.sqrt S).toEuclideanLin z + m)⟫_ℝ)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin p))) =
      (Real.sqrt ((1 + (2 : ℝ) • (S * T)).det))⁻¹ *
        Real.exp (-⟪m, (T * (1 + (2 : ℝ) • (S * T))⁻¹).toEuclideanLin m⟫_ℝ) := by
  have hR := positive_sqrt_isUnit_det hS
  have hA : ((CFC.sqrt S).transpose * T * CFC.sqrt S).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hT.conjTranspose_mul_mul_same (CFC.sqrt S)
  have he (z : EuclideanSpace ℝ (Fin p)) :
      (CFC.sqrt S).toEuclideanLin (z + ((CFC.sqrt S)⁻¹).toEuclideanLin m) =
        (CFC.sqrt S).toEuclideanLin z + m := by
    rw [map_add, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      Matrix.mul_nonsing_inv _ hR, Matrix.toLpLin_one, LinearMap.id_apply]
  simp_rw [← he, quadratic_matrix_congruence]
  rw [matrix_gaussian_laplace hA, quadratic_matrix_congruence,
    sqrt_precision_resolvent hS hT, sqrt_congruence_precision_det hS.posSemidef]

end ResearchMain.WishartBlocks
