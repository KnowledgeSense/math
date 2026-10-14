import MainTheorems.DiagonalSchatten.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

namespace ResearchMain.AHOConstants

open scoped BigOperators
open ResearchMain.DiagonalSchatten

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem trace_product_entries (X Y : Matrix I I ℂ) :
    Matrix.trace (X * Y) = ∑ e : I × I, X e.1 e.2 * Y e.2 e.1 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]

theorem trace_product_norm_square (X Y : Matrix I I ℂ) :
    ‖Matrix.trace (X * Y)‖ ^ 2 ≤ schattenPower 2 X * schattenPower 2 Y := by
  have hn : ‖Matrix.trace (X * Y)‖ ≤
      ∑ e : I × I, ‖X e.1 e.2‖ * ‖Y e.2 e.1‖ := by
    rw [trace_product_entries]
    simpa only [norm_mul] using norm_sum_le Finset.univ
      (fun e : I × I => X e.1 e.2 * Y e.2 e.1)
  have hn' : 0 ≤ ∑ e : I × I, ‖X e.1 e.2‖ * ‖Y e.2 e.1‖ := by positivity
  have hsq : ‖Matrix.trace (X * Y)‖ ^ 2 ≤
      (∑ e : I × I, ‖X e.1 e.2‖ * ‖Y e.2 e.1‖) ^ 2 := by
    nlinarith [norm_nonneg (Matrix.trace (X * Y))]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun e : I × I => ‖X e.1 e.2‖) (fun e : I × I => ‖Y e.2 e.1‖)
  have hx : (∑ e : I × I, ‖X e.1 e.2‖ ^ 2) = schattenPower 2 X := by
    rw [schattenPower_two, Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hy : (∑ e : I × I, ‖Y e.2 e.1‖ ^ 2) = schattenPower 2 Y := by
    rw [schattenPower_two, Fintype.sum_prod_type]
  rw [hx, hy] at hcs
  exact hsq.trans hcs

theorem schattenNorm_two_square (X : Matrix I I ℂ) :
    schattenNorm 2 X ^ 2 = schattenPower 2 X := by
  have h := schattenNorm_rpow 2 (by norm_num) X
  simpa only [Real.rpow_two] using h

theorem trace_product_hilbertSchmidt (X Y : Matrix I I ℂ) :
    ‖Matrix.trace (X * Y)‖ ≤ schattenNorm 2 X * schattenNorm 2 Y := by
  have hs := trace_product_norm_square X Y
  have hp : (schattenNorm 2 X * schattenNorm 2 Y) ^ 2 =
      schattenPower 2 X * schattenPower 2 Y := by
    rw [mul_pow, schattenNorm_two_square, schattenNorm_two_square]
  rw [← hp] at hs
  exact le_of_sq_le_sq hs (mul_nonneg (schattenNorm_nonneg 2 X) (schattenNorm_nonneg 2 Y))

end ResearchMain.AHOConstants
