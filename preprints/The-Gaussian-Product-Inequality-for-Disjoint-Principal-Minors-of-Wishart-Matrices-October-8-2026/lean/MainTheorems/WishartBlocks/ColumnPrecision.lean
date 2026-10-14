import MainTheorems.WishartBlocks.GaussianGammaColumn
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators InnerProductSpace

noncomputable def columnPrecision {n : ℕ} (a : ℝ)
    (b : EuclideanSpace ℝ (Fin n)) (T : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (Matrix.of fun _ _ => a) (Matrix.replicateRow (Fin 1) b)
    (Matrix.replicateCol (Fin 1) b) T

theorem euclidean_dotProduct_matrix {n : ℕ} (x y : EuclideanSpace ℝ (Fin n))
    (T : Matrix (Fin n) (Fin n) ℝ) :
    (fun i => x i) ⬝ᵥ (T *ᵥ fun i => y i) = ⟪x, T.toEuclideanLin y⟫_ℝ := by
  simp [dotProduct, PiLp.inner_apply, Matrix.toLpLin_apply, mul_comm]

theorem columnPrecision_quadratic {n : ℕ} (a d : ℝ)
    (b z : EuclideanSpace ℝ (Fin n)) (T : Matrix (Fin n) (Fin n) ℝ) :
    let v := Sum.elim (fun _ : Fin 1 => d) (fun i => z i)
    v ⬝ᵥ (columnPrecision a b T *ᵥ v) = columnQuadratic a b T d z := by
  dsimp only
  unfold columnPrecision
  rw [Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim,
    dotProduct_add, dotProduct_add]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  have ha : (fun _ : Fin 1 => d) ⬝ᵥ ((Matrix.of fun _ _ : Fin 1 => a) *ᵥ fun _ => d) =
      a * d ^ 2 := by simp [dotProduct, Matrix.mulVec, pow_two]; ring
  have hb : (fun _ : Fin 1 => d) ⬝ᵥ
      (Matrix.replicateRow (Fin 1) b *ᵥ fun i => z i) = d * ⟪b, z⟫_ℝ := by
    simp [dotProduct, Matrix.mulVec, PiLp.inner_apply, Finset.mul_sum, mul_comm]
  have hc : (fun i => z i) ⬝ᵥ
      (Matrix.replicateCol (Fin 1) b *ᵥ fun _ => d) = d * ⟪b, z⟫_ℝ := by
    simp [dotProduct, Matrix.mulVec, PiLp.inner_apply, Finset.mul_sum, mul_comm, mul_assoc]
  rw [ha, hb, hc, euclidean_dotProduct_matrix]
  unfold columnQuadratic
  ring

theorem columnPrecision_quadratic_nonneg {n : ℕ} {a : ℝ}
    {b : EuclideanSpace ℝ (Fin n)} {T : Matrix (Fin n) (Fin n) ℝ}
    (hP : (columnPrecision a b T).PosSemidef) (d : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : 0 ≤ columnQuadratic a b T d z := by
  have h := hP.dotProduct_mulVec_nonneg (Sum.elim (fun _ : Fin 1 => d) (fun i => z i))
  simpa only [star_trivial, columnPrecision_quadratic] using h

theorem columnPrecision_trailing_psd {n : ℕ} {a : ℝ}
    {b : EuclideanSpace ℝ (Fin n)} {T : Matrix (Fin n) (Fin n) ℝ}
    (hP : (columnPrecision a b T).PosSemidef) : T.PosSemidef :=
  hP.submatrix Sum.inr

theorem columnPrecision_det {n : ℕ} {a : ℝ}
    {b : EuclideanSpace ℝ (Fin n)} {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.PosSemidef) :
    (1 + (2 : ℝ) • columnPrecision a b T).det =
      (1 + (2 : ℝ) • T).det * (1 + 2 * columnSchur a b T) := by
  let M := 1 + (2 : ℝ) • T
  have hdet : IsUnit M.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [matrix_one_add_smul_det hT.1]
    apply (Finset.prod_pos _).ne'
    intro i _
    have hEig := hT.eigenvalues_nonneg i
    positivity
  let : Invertible M := M.invertibleOfIsUnitDet hdet
  have he : 1 + (2 : ℝ) • columnPrecision a b T =
      Matrix.fromBlocks (Matrix.of fun _ _ : Fin 1 => 1 + 2 * a)
        (Matrix.replicateRow (Fin 1) ((2 : ℝ) • b))
        (Matrix.replicateCol (Fin 1) ((2 : ℝ) • b)) M := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [columnPrecision, Subsingleton.elim i j]
      | inr j => simp [columnPrecision]
    | inr i =>
      cases j with
      | inl j => simp [columnPrecision]
      | inr j => simp [columnPrecision, M, Matrix.one_apply]
  have hb : (Matrix.replicateRow (Fin 1) ((2 : ℝ) • b) * M⁻¹ *
      Matrix.replicateCol (Fin 1) ((2 : ℝ) • b)) default default =
      4 * ⟪b, (M⁻¹).toEuclideanLin b⟫_ℝ := by
    rw [Matrix.mul_assoc, ← Matrix.replicateCol_mulVec,
      Matrix.replicateRow_mul_replicateCol]
    change ((2 : ℝ) • fun i => b i) ⬝ᵥ
      (M⁻¹ *ᵥ ((2 : ℝ) • fun i => b i)) = _
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, euclidean_dotProduct_matrix]
    ring
  rw [he, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv,
    Matrix.det_unique (n := Fin 1)]
  change M.det * (1 + 2 * a -
    (Matrix.replicateRow (Fin 1) ((2 : ℝ) • b) * M⁻¹ *
      Matrix.replicateCol (Fin 1) ((2 : ℝ) • b)) default default) = _
  rw [hb]
  dsimp [columnSchur, M]
  ring

theorem gamma_column_laplace_determinants {n : ℕ} {a s : ℝ}
    {b : EuclideanSpace ℝ (Fin n)} {T : Matrix (Fin n) (Fin n) ℝ}
    (hP : (columnPrecision a b T).PosSemidef) (hs : 0 < s) :
    ∫ xz, gammaColumnKernel a b T xz
        ∂((gammaMeasure s (1 / 2)).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      (1 + (2 : ℝ) • columnPrecision a b T).det ^ (-s) *
        (1 + (2 : ℝ) • T).det ^ (s - (1 / 2 : ℝ)) := by
  have hT := columnPrecision_trailing_psd hP
  have hQ := columnPrecision_quadratic_nonneg hP
  have hD : 0 < (1 + (2 : ℝ) • T).det := by
    rw [matrix_one_add_smul_det hT.1]
    apply Finset.prod_pos
    intro i _
    have hEig := hT.eigenvalues_nonneg i
    positivity
  have hκ : 0 < 1 + 2 * columnSchur a b T := by
    have h := columnSchur_nonneg hT hQ
    positivity
  rw [gamma_column_laplace hT hs hQ, columnPrecision_det hT,
    Real.mul_rpow hD.le hκ.le, Real.sqrt_eq_rpow]
  rw [← Real.rpow_neg hD.le, mul_right_comm, ← Real.rpow_add hD]
  congr 1
  congr 1
  ring

end ResearchMain.WishartBlocks
