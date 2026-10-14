import MainTheorems.AHOConstants.RealMatrixProducts
import Mathlib.Analysis.MeanInequalities

namespace ResearchMain.AHOConstants

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}

noncomputable def diagonalWeightedMatrix (v : I → ℝ) (p : ℝ) (N : Matrix I I ℝ) :
    Matrix I I ℝ := Matrix.diagonal (fun i => v i ^ p) * N

def singleDiagonalMatrix (v : I → ℝ) (j : Fin (m + 1))
    (N : Fin (m + 1) → Matrix I I ℝ) (i : Fin (m + 1)) : Matrix I I ℝ :=
  if i = j then Matrix.diagonal v * N i else N i

theorem diagonalWeightedMatrix_entry (v : I → ℝ) (p : ℝ) (N : Matrix I I ℝ) (i j : I) :
    diagonalWeightedMatrix v p N i j = v i ^ p * N i j := by
  rw [diagonalWeightedMatrix, Matrix.diagonal_mul]

theorem singleDiagonalMatrix_entry (v : I → ℝ) (j : Fin (m + 1))
    (N : Fin (m + 1) → Matrix I I ℝ) (i : Fin (m + 1)) (a b : I) :
    singleDiagonalMatrix v j N i a b = (if i = j then v a else 1) * N i a b := by
  by_cases hij : i = j
  · simp only [singleDiagonalMatrix, hij, ite_true, Matrix.diagonal_mul]
  · simp only [singleDiagonalMatrix, hij, ite_false, one_mul]

theorem singleDiagonalMatrix_walk_product (v : I → ℝ) (j : Fin (m + 1))
    (N : Fin (m + 1) → Matrix I I ℝ) (f : Fin (m + 1) → I) :
    (∏ i, singleDiagonalMatrix v j N i (f i) (f (finRotate _ i))) =
      v (f j) * ∏ i, N i (f i) (f (finRotate _ i)) := by
  simp_rw [singleDiagonalMatrix_entry]
  rw [Finset.prod_mul_distrib]
  simp

theorem singleDiagonalMatrix_trace (v : I → ℝ) (j : Fin (m + 1))
    (N : Fin (m + 1) → Matrix I I ℝ) :
    Matrix.trace (List.ofFn (singleDiagonalMatrix v j N)).prod =
      ∑ f : Fin (m + 1) → I, v (f j) * ∏ i, N i (f i) (f (finRotate _ i)) := by
  rw [closed_walk_trace_ofFn]
  simp_rw [singleDiagonalMatrix_walk_product]

theorem diagonal_weight_trace_AMGM (v : I → ℝ) (hv : ∀ i, 0 ≤ v i)
    (p : Fin (m + 1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : (∑ i, p i) = 1)
    (N : Fin (m + 1) → Matrix I I ℝ) (hN : ∀ i, EntryNonnegative (N i)) :
    Matrix.trace (List.ofFn (fun i => diagonalWeightedMatrix v (p i) (N i))).prod ≤
      ∑ j, p j * Matrix.trace (List.ofFn (singleDiagonalMatrix v j N)).prod := by
  let coeff : (Fin (m + 1) → I) → ℝ := fun f => ∏ i, N i (f i) (f (finRotate _ i))
  have hc : ∀ f, 0 ≤ coeff f := fun f => Finset.prod_nonneg (fun i hi => hN i _ _)
  have hterm : ∀ f : Fin (m + 1) → I,
      (∏ i, diagonalWeightedMatrix v (p i) (N i) (f i) (f (finRotate _ i))) ≤
        (∑ i, p i * v (f i)) * coeff f := by
    intro f
    simp_rw [diagonalWeightedMatrix_entry]
    rw [Finset.prod_mul_distrib]
    have hmean : (∏ i, v (f i) ^ p i) ≤ ∑ i, p i * v (f i) := by
      simpa using Real.geom_mean_le_arith_mean_weighted Finset.univ p (fun i => v (f i))
        (fun i hi => hp i) (by simpa using hsum) (fun i hi => hv (f i))
    exact mul_le_mul_of_nonneg_right hmean (hc f)
  rw [closed_walk_trace_ofFn]
  calc
    _ ≤ ∑ f : Fin (m + 1) → I, (∑ i, p i * v (f i)) * coeff f :=
      Finset.sum_le_sum (fun f hf => hterm f)
    _ = ∑ i, p i * (∑ f : Fin (m + 1) → I, v (f i) * coeff f) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      ring
    _ = _ := by simp only [singleDiagonalMatrix_trace, coeff]

end ResearchMain.AHOConstants
