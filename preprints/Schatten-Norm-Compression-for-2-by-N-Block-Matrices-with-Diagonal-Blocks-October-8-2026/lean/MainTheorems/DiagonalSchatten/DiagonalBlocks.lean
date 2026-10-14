import MainTheorems.DiagonalSchatten.Basic

namespace ResearchMain.DiagonalSchatten

open scoped BigOperators

variable {J D : Type*} [Fintype J] [Fintype D] [DecidableEq J] [DecidableEq D]

def diagonalBlock (z : Fin 2 → J → D → ℂ) (i : Fin 2) (j : J) : Matrix D D ℂ :=
  Matrix.diagonal (z i j)

def diagonalBlockMatrix (z : Fin 2 → J → D → ℂ) :
    Matrix (Fin 2 × D) (J × D) ℂ :=
  fun i j => if i.2 = j.2 then z i.1 j.1 i.2 else 0

noncomputable def compression (p : ℝ) (z : Fin 2 → J → D → ℂ) : Matrix (Fin 2) J ℂ :=
  fun i j => (schattenNorm p (diagonalBlock z i j) : ℂ)

omit [Fintype J] [DecidableEq J] in
theorem diagonalBlock_schattenPower_two (z : Fin 2 → J → D → ℂ) (i : Fin 2) (j : J) :
    schattenPower 2 (diagonalBlock z i j) = ∑ d, ‖z i j d‖ ^ 2 := by
  rw [schattenPower_two]
  simp [diagonalBlock, Matrix.diagonal, apply_ite]

omit [Fintype J] [DecidableEq J] in
theorem diagonalBlock_schattenNorm_two_sq (z : Fin 2 → J → D → ℂ)
    (i : Fin 2) (j : J) :
    schattenNorm 2 (diagonalBlock z i j) ^ 2 = ∑ d, ‖z i j d‖ ^ 2 := by
  rw [← Real.rpow_two, schattenNorm_rpow 2 (by norm_num), diagonalBlock_schattenPower_two]

theorem diagonalBlockMatrix_schattenPower_two (z : Fin 2 → J → D → ℂ) :
    schattenPower 2 (diagonalBlockMatrix z) = ∑ j, ∑ i : Fin 2, ∑ d, ‖z i j d‖ ^ 2 := by
  rw [schattenPower_two]
  simp only [Fintype.sum_prod_type, diagonalBlockMatrix]
  simp only [apply_ite, norm_zero, zero_pow (by decide : 2 ≠ 0), ite_pow,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

theorem compression_schattenPower_two (z : Fin 2 → J → D → ℂ) :
    schattenPower 2 (compression 2 z) = ∑ j, ∑ i : Fin 2, ∑ d, ‖z i j d‖ ^ 2 := by
  rw [schattenPower_two]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [compression, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (schattenNorm_nonneg 2 (diagonalBlock z i j)),
    diagonalBlock_schattenNorm_two_sq]

theorem diagonal_compression_two (z : Fin 2 → J → D → ℂ) :
    schattenNorm 2 (diagonalBlockMatrix z) = schattenNorm 2 (compression 2 z) := by
  unfold schattenNorm
  rw [diagonalBlockMatrix_schattenPower_two, compression_schattenPower_two]

end ResearchMain.DiagonalSchatten
