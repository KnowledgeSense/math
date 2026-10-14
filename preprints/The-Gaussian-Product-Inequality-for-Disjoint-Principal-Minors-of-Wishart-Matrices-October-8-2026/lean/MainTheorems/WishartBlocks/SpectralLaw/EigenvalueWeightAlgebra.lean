import MainTheorems.WishartBlocks.SpectralLaw.WishartCoordinateDensity
import MainTheorems.WishartBlocks.SpectralLaw.SpectralIntegral
import MainTheorems.WishartBlocks.EigenvalueLattice
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace ResearchMain.WishartBlocks

open scoped BigOperators

theorem orthogonal_congruence_trace {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (W : Matrix (Fin n) (Fin n) ℝ) :
    (matrixCongruence (U : Matrix (Fin n) (Fin n) ℝ) W).trace = W.trace := by
  have hu : (U : Matrix (Fin n) (Fin n) ℝ).transpose *
      (U : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.star_mul_self_of_mem U.property
  simpa only [Matrix.one_mul, Matrix.mul_one, hu] using
    trace_matrixCongruence (U : Matrix (Fin n) (Fin n) ℝ) 1 W

theorem wishartDensityReal_orthogonal_congruence {n : ℕ} (α : ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (W : Matrix (Fin n) (Fin n) ℝ) :
    wishartDensityReal α (matrixCongruence (U : Matrix (Fin n) (Fin n) ℝ) W) =
      wishartDensityReal α W := by
  unfold wishartDensityReal
  rw [orthogonal_congruence_det, orthogonal_congruence_trace]

theorem wishartDensityReal_diagonal_gap {n : ℕ} (α : ℝ) {lam : Fin n → ℝ}
    (hlam : OrderedPositive lam) :
    wishartDensityReal α (Matrix.diagonal lam) * gapProduct lam =
      wishartDensityCoefficient n α * eigenvalueWeight α lam := by
  classical
  unfold wishartDensityReal eigenvalueWeight chamberWeight
  rw [ite_eq_left hlam, Matrix.det_diagonal, Matrix.trace_diagonal,
    Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ (fun i _ => (hlam.1 i).le),
    ← Real.exp_sum]
  have he : (∑ i : Fin n, -lam i / 2) = -(∑ i : Fin n, lam i) / 2 := by
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
  rw [he]
  ring

theorem wishartDensityReal_orthogonal_diagonal_gap {n : ℕ} (α : ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) {lam : Fin n → ℝ} (hlam : OrderedPositive lam) :
    wishartDensityReal α
        (matrixCongruence (U : Matrix (Fin n) (Fin n) ℝ) (Matrix.diagonal lam)) * gapProduct lam =
      wishartDensityCoefficient n α * eigenvalueWeight α lam := by
  rw [wishartDensityReal_orthogonal_congruence]
  exact wishartDensityReal_diagonal_gap α hlam

end ResearchMain.WishartBlocks
