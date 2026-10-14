import MainTheorems.WishartBlocks.GaussianAffineLaplace

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators MatrixOrder InnerProductSpace

theorem matrix_resolvent_positiveSemidefinite {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) : (A * (1 + c • A)⁻¹).PosSemidef := by
  let N := 1 + c • A
  have hN : N.PosSemidef := Matrix.PosSemidef.one.add (hA.smul hc)
  have hdet : IsUnit N.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [matrix_one_add_smul_det hA.1]
    apply ne_of_gt
    apply Finset.prod_pos
    intro i _
    have hi := hA.eigenvalues_nonneg i
    positivity
  have hAN : A * N = N * A := by
    simp only [N, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  have hAI : A * N⁻¹ = N⁻¹ * A := by
    calc
      _ = (N⁻¹ * N) * A * N⁻¹ := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
      _ = N⁻¹ * (N * A) * N⁻¹ := by simp only [Matrix.mul_assoc]
      _ = N⁻¹ * (A * N) * N⁻¹ := by rw [hAN]
      _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  have hH : (A * N⁻¹).IsHermitian := by
    apply (Matrix.IsHermitian.commute_iff hA.1 hN.1.inv).mp
    exact hAI
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  have he : star x ⬝ᵥ ((A * N⁻¹) *ᵥ x) =
      ⟪y, (A * (1 + c • A)⁻¹).toEuclideanLin y⟫_ℝ := by
    rw [← euclidean_dotProduct_matrix]
    simp only [star_trivial]
    rfl
  rw [he, matrix_resolvent_quadratic hA hc]
  apply Finset.sum_nonneg
  intro i _
  have hi := hA.eigenvalues_nonneg i
  positivity

theorem covariance_resolvent_positiveSemidefinite {p : ℕ}
    {S T : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hT : T.PosSemidef) :
    (T * (1 + (2 : ℝ) • (S * T))⁻¹).PosSemidef := by
  have hA : ((CFC.sqrt S).transpose * T * CFC.sqrt S).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hT.conjTranspose_mul_mul_same (CFC.sqrt S)
  have hR := matrix_resolvent_positiveSemidefinite hA (by norm_num : (0 : ℝ) ≤ 2)
  have hC := hR.conjTranspose_mul_mul_same (CFC.sqrt S)⁻¹
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
    sqrt_precision_resolvent hS hT] using hC

end ResearchMain.WishartBlocks
