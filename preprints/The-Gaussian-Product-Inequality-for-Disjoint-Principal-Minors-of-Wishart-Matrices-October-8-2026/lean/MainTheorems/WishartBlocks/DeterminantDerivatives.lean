import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace ResearchMain.WishartBlocks

open scoped Matrix.Norms.L2Operator

theorem determinant_identity_directional {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • H).det) H.trace 0 := by
  let P := (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • H.map Polynomial.C)).divX.divX
  have h := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
    ((hasDerivAt_id' (0 : ℝ)).const_mul H.trace)).add
    ((P.hasDerivAt 0).mul ((hasDerivAt_id' (0 : ℝ)).pow 2))
  have h' : HasDerivAt (fun t : ℝ => 1 + H.trace * t + P.eval t * t ^ 2)
      H.trace 0 := by
    convert! h using 1
    simp
  convert h' using 1
  ext t
  exact Matrix.det_one_add_smul t H

theorem determinant_directional {n : ℕ} (A H : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) :
    HasDerivAt (fun t : ℝ => (A + t • H).det) (A.det * (A⁻¹ * H).trace) 0 := by
  have h := (determinant_identity_directional (A⁻¹ * H)).const_mul A.det
  convert h using 1
  ext t
  have hM : A + t • H = A * (1 + t • (A⁻¹ * H)) := by
    rw [mul_add, mul_one, mul_smul_comm, ← mul_assoc,
      Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), one_mul]
  rw [hM, Matrix.det_mul]

theorem determinant_directional_at {n : ℕ} (A H : Matrix (Fin n) (Fin n) ℝ)
    (s : ℝ) (hA : (A + s • H).det ≠ 0) :
    HasDerivAt (fun t : ℝ => (A + t • H).det)
      ((A + s • H).det * ((A + s • H)⁻¹ * H).trace) s := by
  have h := (determinant_directional (A + s • H) H hA).comp_of_eq s
    ((hasDerivAt_id' s).sub_const s) (by simp)
  convert h using 1
  · ext t
    congr 1
    module
  · simp

theorem determinant_power_directional {n : ℕ} (A H : Matrix (Fin n) (Fin n) ℝ)
    (hA : 0 < A.det) (b : ℝ) :
    HasDerivAt (fun t : ℝ => (A + t • H).det ^ b)
      (A.det ^ b * (b * (A⁻¹ * H).trace)) 0 := by
  have h := (determinant_directional A H hA.ne').rpow_const (p := b)
    (Or.inl (by simpa using hA.ne'))
  have hp : A.det ^ (b - 1) * A.det = A.det ^ b := by
    simpa only [sub_add_cancel] using (Real.rpow_add_one hA.ne' (b - 1)).symm
  convert h using 1
  simp only [zero_smul, add_zero]
  calc
    A.det ^ b * (b * (A⁻¹ * H).trace) =
        (A.det ^ (b - 1) * A.det) * (b * (A⁻¹ * H).trace) := by rw [hp]
    _ = (A.det * (A⁻¹ * H).trace) * b * A.det ^ (b - 1) := by ring

theorem inverse_directional {n : ℕ} (A H : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) :
    HasDerivAt (fun t : ℝ => (A + t • H)⁻¹) (-(A⁻¹ * H * A⁻¹)) 0 := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)
  have hi : (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) = A⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  have hd : HasDerivAt (fun t : ℝ => A + t • H) H 0 := by
    convert! (hasDerivAt_const (0 : ℝ) A).add
      ((hasDerivAt_id' (0 : ℝ)).smul_const H) using 1
    simp
  have hh := (hasFDerivAt_ringInverse (𝕜 := ℝ) u).comp_hasDerivAt_of_eq (0 : ℝ) hd
    (by simpa using hu)
  simpa only [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse,
    neg_apply, ContinuousLinearMap.mulLeftRight_apply, hi] using hh

theorem inverse_trace_directional {n : ℕ} (A H K : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) :
    HasDerivAt (fun t : ℝ => ((A + t • K)⁻¹ * H).trace)
      (-(A⁻¹ * K * A⁻¹ * H).trace) 0 := by
  let T := (Matrix.traceLinearMap (Fin n) ℝ ℝ).toContinuousLinearMap
  have hi := (inverse_directional A K hA).mul_const H
  have ht := T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hi
  simpa only [Function.comp_def, T, LinearMap.coe_toContinuousLinearMap',
    Matrix.traceLinearMap_apply, neg_mul, Matrix.trace_neg] using ht

theorem determinant_power_hessian_directional {n : ℕ}
    (A H K : Matrix (Fin n) (Fin n) ℝ) (hA : 0 < A.det) (b : ℝ) :
    HasDerivAt
      (fun t : ℝ => (A + t • K).det ^ b * (b * ((A + t • K)⁻¹ * H).trace))
      (A.det ^ b * (b ^ 2 * (A⁻¹ * H).trace * (A⁻¹ * K).trace -
        b * (A⁻¹ * K * A⁻¹ * H).trace)) 0 := by
  have h := (determinant_power_directional A K hA b).mul
    ((inverse_trace_directional A H K hA.ne').const_mul b)
  convert h using 1
  simp only [zero_smul, add_zero]
  ring

end ResearchMain.WishartBlocks
