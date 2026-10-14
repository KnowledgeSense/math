import MainTheorems.WishartBlocks.WishartRegressionKernel
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace ResearchMain.WishartBlocks

open Matrix
open scoped MatrixOrder

noncomputable def regressionCovariance {k m : ℕ}
    (A : Matrix (Fin k) (Fin k) ℝ) (S : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin k) (Fin m) ℝ) :
    Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℝ :=
  Matrix.fromBlocks A (A * K) (K.transpose * A) (S + K.transpose * A * K)

theorem regression_precision_blocks {k m : ℕ}
    (A T : Matrix (Fin k) (Fin k) ℝ) (S U : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin k) (Fin m) ℝ) :
    1 + (2 : ℝ) • (regressionCovariance A S K * Matrix.fromBlocks T 0 0 U) =
      Matrix.fromBlocks (1 + (2 : ℝ) • (A * T)) ((2 : ℝ) • (A * K * U))
        ((2 : ℝ) • (K.transpose * A * T))
        (1 + (2 : ℝ) • ((S + K.transpose * A * K) * U)) := by
  unfold regressionCovariance
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, zero_add, add_zero]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
  simp only [zero_add]

theorem regression_precision_det {k m : ℕ}
    (A T : Matrix (Fin k) (Fin k) ℝ) {S U : Matrix (Fin m) (Fin m) ℝ}
    (hS : S.PosSemidef) (hU : U.PosSemidef) (K : Matrix (Fin k) (Fin m) ℝ) :
    (1 + (2 : ℝ) • (regressionCovariance A S K * Matrix.fromBlocks T 0 0 U)).det =
      (1 + (2 : ℝ) • (S * U)).det *
        (1 + (2 : ℝ) • (A *
          (T + K * (U * (1 + (2 : ℝ) • (S * U))⁻¹) * K.transpose))).det := by
  let D := 1 + (2 : ℝ) • (S * U)
  let P := 1 + (2 : ℝ) • (regressionCovariance A S K * Matrix.fromBlocks T 0 0 U)
  let L : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℝ :=
    Matrix.fromBlocks 1 0 (-K.transpose) 1
  have hD : IsUnit D.det := isUnit_iff_ne_zero.mpr
    (covariance_precision_det_pos hS hU).ne'
  let : Invertible D := D.invertibleOfIsUnitDet hD
  have hL : L.det = 1 := by
    dsimp only [L]
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one, one_mul]
  have hLP : L * P =
      Matrix.fromBlocks (1 + (2 : ℝ) • (A * T)) ((2 : ℝ) • (A * K * U))
        (-K.transpose) D := by
    dsimp only [L, P]
    rw [regression_precision_blocks, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, add_zero, Matrix.one_mul]
    congr 1 <;>
      simp only [D, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
        Matrix.mul_smul, Matrix.neg_mul,
        Matrix.mul_assoc] <;> module
  have hSchur : (1 + (2 : ℝ) • (A * T)) -
      ((2 : ℝ) • (A * K * U)) * D⁻¹ * (-K.transpose) =
        1 + (2 : ℝ) • (A * (T + K * (U * D⁻¹) * K.transpose)) := by
    simp only [Matrix.mul_add, Matrix.smul_mul, Matrix.mul_neg,
      Matrix.mul_assoc]
    module
  calc
    _ = (L * P).det := by rw [Matrix.det_mul, hL, one_mul]
    _ = D.det * ((1 + (2 : ℝ) • (A * T)) -
        ((2 : ℝ) • (A * K * U)) * D⁻¹ * (-K.transpose)).det := by
      rw [hLP, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
    _ = _ := by rw [hSchur]

end ResearchMain.WishartBlocks
