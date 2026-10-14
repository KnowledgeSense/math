import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

open scoped MatrixOrder

theorem inverse_sandwich_le {n : ℕ} {A W : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hWA : W ≤ A) : A⁻¹ * W * A⁻¹ ≤ A⁻¹ := by
  have hG := hA.posSemidef.inv
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hAW : (A - W).PosSemidef := hWA
  change (A⁻¹ - A⁻¹ * W * A⁻¹).PosSemidef
  simpa only [hG.isHermitian.eq, mul_sub, sub_mul, Matrix.nonsing_inv_mul A hu, one_mul] using
    hAW.conjTranspose_mul_mul_same A⁻¹

theorem inverse_trace_bounds {n : ℕ} {A W : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hW : W.PosSemidef) (hWA : W ≤ A) :
    0 ≤ (A⁻¹ * W).trace ∧ (A⁻¹ * W).trace ≤ n := by
  let S := CFC.sqrt A
  let R := S⁻¹
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hSd : 0 < S.det := by
    change 0 < (CFC.sqrt A).det
    rw [hA.posSemidef.det_sqrt, RCLike.sqrt_real]
    exact Real.sqrt_pos.mpr hA.det_pos
  have hu : IsUnit S.det := isUnit_iff_ne_zero.mpr hSd.ne'
  have hRS : R * S = 1 := Matrix.nonsing_inv_mul S hu
  have hSR : S * R = 1 := Matrix.mul_nonsing_inv S hu
  have hR : R.PosSemidef := hS.inv
  have hRA : R * A * R = 1 := by
    rw [← hSS]
    calc
      R * (S * S) * R = (R * S) * (S * R) := by simp only [mul_assoc]
      _ = 1 := by rw [hRS, hSR, one_mul]
  have hRR : R * R = A⁻¹ := by
    change S⁻¹ * S⁻¹ = A⁻¹
    rw [← Matrix.mul_inv_rev, hSS]
  have hRW : (R * W * R).PosSemidef := by
    simpa only [hR.isHermitian.eq] using hW.mul_mul_conjTranspose_same R
  have hAW : (A - W).PosSemidef := hWA
  have hKR : (1 - R * W * R).PosSemidef := by
    simpa only [hR.isHermitian.eq, mul_sub, sub_mul, hRA] using
      hAW.mul_mul_conjTranspose_same R
  have ht : (R * W * R).trace = (A⁻¹ * W).trace := by
    rw [Matrix.trace_mul_cycle, hRR]
  constructor
  · simpa only [ht] using hRW.trace_nonneg
  · have hh := hKR.trace_nonneg
    rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, ht] at hh
    linarith

theorem determinant_block_operator_positiveSemidefinite {n : ℕ}
    {A W : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hW : W.PosSemidef) (hWA : W ≤ A)
    {q b : ℝ} (hq : (n : ℝ) + 1 ≤ q) (hb : 0 ≤ b) :
    (b • ((q - (A⁻¹ * W).trace) • A⁻¹ - A⁻¹ * W * A⁻¹)).PosSemidef := by
  have ht := inverse_trace_bounds hA hW hWA
  have hc : 0 ≤ q - (A⁻¹ * W).trace - 1 := by linarith
  have hG := hA.posSemidef.inv
  have hs : (A⁻¹ - A⁻¹ * W * A⁻¹).PosSemidef := inverse_sandwich_le hA hWA
  have hsum := (hG.smul hc).add hs
  have hp : ((q - (A⁻¹ * W).trace) • A⁻¹ - A⁻¹ * W * A⁻¹).PosSemidef := by
    convert hsum using 1
    module
  exact hp.smul hb

end ResearchMain.WishartBlocks
