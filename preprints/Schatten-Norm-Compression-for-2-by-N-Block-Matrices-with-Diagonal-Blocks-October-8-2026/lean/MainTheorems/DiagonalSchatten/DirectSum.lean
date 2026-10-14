import MainTheorems.DiagonalSchatten.GramSpectrum
import MainTheorems.DiagonalSchatten.DiagonalBlocks
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace ResearchMain.DiagonalSchatten

open scoped BigOperators Polynomial

variable {I J D : Type*} [Fintype I] [Fintype J] [Fintype D]
  [DecidableEq I] [DecidableEq J] [DecidableEq D]

theorem charmatrix_blockDiagonal (A : D → Matrix I I ℂ) :
    (Matrix.blockDiagonal A).charmatrix =
      Matrix.blockDiagonal fun d => (A d).charmatrix := by
  ext ⟨i, d⟩ ⟨j, e⟩
  by_cases hde : d = e
  · subst e
    simp [Matrix.charmatrix_apply, Matrix.blockDiagonal, Matrix.diagonal_apply]
  · simp [Matrix.charmatrix_apply, Matrix.blockDiagonal, Matrix.diagonal_apply, hde,
      Prod.mk.injEq]

theorem charpoly_blockDiagonal (A : D → Matrix I I ℂ) :
    (Matrix.blockDiagonal A).charpoly = ∏ d, (A d).charpoly := by
  unfold Matrix.charpoly
  rw [charmatrix_blockDiagonal, Matrix.det_blockDiagonal]

theorem rootPowerSum_blockDiagonal (p : ℝ) (A : D → Matrix I I ℂ) :
    rootPowerSum p (Matrix.blockDiagonal A) = ∑ d, rootPowerSum p (A d) := by
  rw [rootPowerSum, charpoly_blockDiagonal,
    Polynomial.roots_prod (fun d => (A d).charpoly) Finset.univ
      (Finset.prod_ne_zero_iff.mpr fun d _ => (Matrix.charpoly_monic (A d)).ne_zero)]
  simp only [Multiset.map_bind]
  change (Finset.univ.val.bind fun d =>
    ((A d).charpoly.roots.map fun z => (Real.sqrt z.re) ^ p)).sum =
      ∑ d, rootPowerSum p (A d)
  induction (Finset.univ : Finset D) using Finset.induction_on with
  | empty => simp
  | @insert d s hd ih =>
      simp only [Finset.insert_val_of_notMem hd, Multiset.cons_bind, Multiset.sum_add,
        Finset.sum_insert hd, rootPowerSum]
      rw [ih]
      rfl

theorem schattenPower_blockDiagonal (p : ℝ) (A : D → Matrix I J ℂ) :
    schattenPower p (Matrix.blockDiagonal A) = ∑ d, schattenPower p (A d) := by
  rw [schattenPower_eq_gram_roots, Matrix.blockDiagonal_conjTranspose,
    ← Matrix.blockDiagonal_mul, rootPowerSum_blockDiagonal]
  apply Finset.sum_congr rfl
  intro d _
  exact (schattenPower_eq_gram_roots p (A d)).symm

theorem diagonalBlockMatrix_schattenPower (p : ℝ) (z : Fin 2 → J → D → ℂ) :
    schattenPower p (diagonalBlockMatrix z) =
      ∑ d, schattenPower p (fun i j => z i j d : Matrix (Fin 2) J ℂ) := by
  change schattenPower p (Matrix.blockDiagonal
    (fun d => (fun i j => z i j d : Matrix (Fin 2) J ℂ))) = _
  exact schattenPower_blockDiagonal p _

end ResearchMain.DiagonalSchatten
