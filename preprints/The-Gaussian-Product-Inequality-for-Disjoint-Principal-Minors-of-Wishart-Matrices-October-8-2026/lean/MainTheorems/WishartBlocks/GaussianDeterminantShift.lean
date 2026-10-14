import MainTheorems.WishartBlocks.GaussianQuadraticMeans
import MainTheorems.WishartBlocks.RankOneWishartLaw
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder InnerProductSpace

theorem positiveSemidefinite_inner_nonneg {p : ℕ}
    {A : Matrix (Fin p) (Fin p) ℝ} (hA : A.PosSemidef)
    (y : EuclideanSpace ℝ (Fin p)) : 0 ≤ ⟪y, A.toEuclideanLin y⟫_ℝ := by
  rw [← euclidean_dotProduct_matrix]
  simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg (fun i => y i)

theorem determinant_rankOne_add {p : ℕ} {V : Matrix (Fin p) (Fin p) ℝ}
    (hV : IsUnit V.det) (y : EuclideanSpace ℝ (Fin p)) :
    (V + Matrix.vecMulVec (fun i => y i) (fun i => y i)).det =
      V.det * (1 + ⟪y, V⁻¹.toEuclideanLin y⟫_ℝ) := by
  have hf : V + Matrix.vecMulVec (fun i => y i) (fun i => y i) =
      V * (1 + V⁻¹ * Matrix.vecMulVec (fun i => y i) (fun i => y i)) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hV, Matrix.one_mul]
  rw [hf, Matrix.det_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_eq (ι := Fin 1),
    Matrix.det_one_add_replicateCol_mul_replicateRow,
    euclidean_dotProduct_matrix]

theorem determinant_rankOne_add_power {p : ℕ} {V : Matrix (Fin p) (Fin p) ℝ}
    (hV : V.PosDef) (y : EuclideanSpace ℝ (Fin p)) (b : ℝ) :
    (V + Matrix.vecMulVec (fun i => y i) (fun i => y i)).det ^ b =
      V.det ^ b * (1 + ⟪y, V⁻¹.toEuclideanLin y⟫_ℝ) ^ b := by
  rw [determinant_rankOne_add (isUnit_iff_ne_zero.mpr hV.det_pos.ne')]
  exact Real.mul_rpow hV.det_pos.le
    (by linarith [positiveSemidefinite_inner_nonneg hV.posSemidef.inv y])

theorem determinant_gaussian_shift_integrable {p : ℕ} {b : ℝ} (hb : 0 ≤ b)
    {V S : Matrix (Fin p) (Fin p) ℝ} (hV : V.PosDef) (hS : S.PosDef)
    (m : EuclideanSpace ℝ (Fin p)) :
    Integrable
      (fun z : EuclideanSpace ℝ (Fin p) => (V + gaussianMeanGram S m z).det ^ b)
      (stdGaussian (EuclideanSpace ℝ (Fin p))) := by
  have hR := positive_sqrt_isUnit_det hS
  have hA : ((CFC.sqrt S).transpose * V⁻¹ * CFC.sqrt S).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.posSemidef.inv.conjTranspose_mul_mul_same (CFC.sqrt S)
  have he (z : EuclideanSpace ℝ (Fin p)) :
      (CFC.sqrt S).toEuclideanLin (z + ((CFC.sqrt S)⁻¹).toEuclideanLin m) =
        (CFC.sqrt S).toEuclideanLin z + m := by
    rw [map_add, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      Matrix.mul_nonsing_inv _ hR, Matrix.toLpLin_one, LinearMap.id_apply]
  simp_rw [gaussianMeanGram, determinant_rankOne_add_power hV,
    ← he, quadratic_matrix_congruence]
  exact (gaussian_matrix_quadratic_integrable (by norm_num : (0 : ℝ) < 1)
    hb hA _).const_mul _

theorem determinant_gaussian_shift_ray_monotone {p : ℕ} {b : ℝ} (hb : 0 ≤ b)
    {V S : Matrix (Fin p) (Fin p) ℝ} (hV : V.PosDef) (hS : S.PosDef)
    (v : EuclideanSpace ℝ (Fin p)) :
    MonotoneOn
      (fun θ => ∫ z : EuclideanSpace ℝ (Fin p),
        (V + gaussianMeanGram S (Real.sqrt θ • v) z).det ^ b
        ∂(stdGaussian (EuclideanSpace ℝ (Fin p)))) (Set.Ici 0) := by
  have hR := positive_sqrt_isUnit_det hS
  have hA : ((CFC.sqrt S).transpose * V⁻¹ * CFC.sqrt S).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.posSemidef.inv.conjTranspose_mul_mul_same (CFC.sqrt S)
  have he (θ : ℝ) (z : EuclideanSpace ℝ (Fin p)) :
      (CFC.sqrt S).toEuclideanLin
          (z + Real.sqrt θ • ((CFC.sqrt S)⁻¹).toEuclideanLin v) =
        (CFC.sqrt S).toEuclideanLin z + Real.sqrt θ • v := by
    rw [map_add, map_smul, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      Matrix.mul_nonsing_inv _ hR, Matrix.toLpLin_one, LinearMap.id_apply]
  simp_rw [gaussianMeanGram, determinant_rankOne_add_power hV,
    ← he, quadratic_matrix_congruence, integral_const_mul]
  intro θ hθ η hη hθη
  exact mul_le_mul_of_nonneg_left
    (gaussian_matrix_quadratic_ray_monotone (by norm_num : (0 : ℝ) < 1)
      hb hA _ hθ hη hθη) (Real.rpow_nonneg hV.det_pos.le b)

end ResearchMain.WishartBlocks
