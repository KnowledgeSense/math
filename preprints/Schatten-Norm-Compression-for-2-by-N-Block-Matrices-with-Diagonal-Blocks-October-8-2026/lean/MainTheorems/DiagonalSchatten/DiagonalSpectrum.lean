import MainTheorems.DiagonalSchatten.GramSpectrum
import MainTheorems.DiagonalSchatten.DiagonalBlocks

namespace ResearchMain.DiagonalSchatten

open scoped BigOperators Polynomial

variable {I J D : Type*} [Fintype I] [Fintype J] [Fintype D]
  [DecidableEq I] [DecidableEq J] [DecidableEq D]

omit [Fintype J] [Fintype D] [DecidableEq J] [DecidableEq D] in
theorem rootPowerSum_diagonal (p : ℝ) (v : I → ℂ) :
    rootPowerSum p (Matrix.diagonal v) = ∑ i, (Real.sqrt (v i).re) ^ p := by
  rw [rootPowerSum, Matrix.charpoly_diagonal,
    Polynomial.roots_prod (fun i => Polynomial.X - Polynomial.C (v i)) Finset.univ
      (Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero (v i))]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map,
    Function.comp_def]
  rfl

omit [Fintype J] [Fintype D] [DecidableEq J] [DecidableEq D] in
theorem schattenPower_diagonal (p : ℝ) (v : I → ℂ) :
    schattenPower p (Matrix.diagonal v) = ∑ i, ‖v i‖ ^ p := by
  rw [schattenPower_eq_gram_roots, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, rootPowerSum_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  change (Real.sqrt ((star (v i) * v i).re)) ^ p = ‖v i‖ ^ p
  have h : (star (v i) * v i).re = ‖v i‖ ^ 2 := by
    simpa [← Complex.ofReal_pow] using congrArg Complex.re (Complex.conj_mul' (v i))
  rw [h, Real.sqrt_sq (norm_nonneg (v i))]

omit [Fintype J] [Fintype D] [DecidableEq J] [DecidableEq D] in
theorem schattenNorm_diagonal (p : ℝ) (v : I → ℂ) :
    schattenNorm p (Matrix.diagonal v) = (∑ i, ‖v i‖ ^ p) ^ (1 / p) := by
  unfold schattenNorm
  rw [schattenPower_diagonal]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem diagonalBlock_schattenPower (p : ℝ) (z : Fin 2 → J → D → ℂ)
    (i : Fin 2) (j : J) :
    schattenPower p (diagonalBlock z i j) = ∑ d, ‖z i j d‖ ^ p :=
  schattenPower_diagonal p (z i j)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem compression_norm_entry (p : ℝ) (z : Fin 2 → J → D → ℂ)
    (i : Fin 2) (j : J) :
    ‖compression p z i j‖ = (∑ d, ‖z i j d‖ ^ p) ^ (1 / p) := by
  rw [compression, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (schattenNorm_nonneg p (diagonalBlock z i j))]
  exact schattenNorm_diagonal p (z i j)

end ResearchMain.DiagonalSchatten
