import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

open MeasureTheory
open scoped MatrixOrder

def positiveCoordinates {n : ℕ} (eigenvalues : Fin n → ℝ) : Fin n → ℝ := fun i => max 0 (eigenvalues i)

noncomputable def spectralMatrix {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (eigenvalues : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  U * Matrix.diagonal (positiveCoordinates eigenvalues) * U.transpose

theorem positiveCoordinates_monotone (n : ℕ) : Monotone (positiveCoordinates (n := n)) := by
  intro eigenvalues η h i
  exact max_le_max le_rfl (h i)

theorem spectralMatrix_positiveSemidefinite {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (eigenvalues : Fin n → ℝ) : (spectralMatrix U eigenvalues).PosSemidef := by
  have h := (Matrix.PosSemidef.diagonal (fun i => le_max_left 0 (eigenvalues i))).mul_mul_conjTranspose_same U
  change (U * Matrix.diagonal (fun i => max 0 (eigenvalues i)) * U.transpose).PosSemidef
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem spectralMatrix_monotone {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) :
    Monotone (spectralMatrix U) := by
  intro eigenvalues η h
  change (spectralMatrix U η - spectralMatrix U eigenvalues).PosSemidef
  have hd : (Matrix.diagonal (positiveCoordinates η - positiveCoordinates eigenvalues)).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i => sub_nonneg.mpr (positiveCoordinates_monotone n h i)
  have he : U * Matrix.diagonal (positiveCoordinates η - positiveCoordinates eigenvalues) *
        U.transpose = spectralMatrix U η - spectralMatrix U eigenvalues := by
    unfold spectralMatrix
    change U * Matrix.diagonal (fun i => positiveCoordinates η i - positiveCoordinates eigenvalues i) *
      U.transpose = _
    rw [← Matrix.diagonal_sub, mul_sub, sub_mul]
  have hp := hd.mul_mul_conjTranspose_same U
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, he] at hp
  exact hp

noncomputable def spectralAverage {n : ℕ} (π : Measure (Matrix (Fin n) (Fin n) ℝ))
    (G : Matrix (Fin n) (Fin n) ℝ → ℝ) (eigenvalues : Fin n → ℝ) : ℝ :=
  ∫ U, G (spectralMatrix U eigenvalues) ∂π

theorem spectralAverage_nonneg {n : ℕ} (π : Measure (Matrix (Fin n) (Fin n) ℝ))
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (hG : ∀ A, A.PosSemidef → 0 ≤ G A) (eigenvalues : Fin n → ℝ) :
    0 ≤ spectralAverage π G eigenvalues :=
  integral_nonneg fun U => hG _ (spectralMatrix_positiveSemidefinite U eigenvalues)

theorem spectralAverage_monotone {n : ℕ} (π : Measure (Matrix (Fin n) (Fin n) ℝ))
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (hG : MonotoneOn G {A | A.PosSemidef})
    (hi : ∀ eigenvalues, Integrable (fun U => G (spectralMatrix U eigenvalues)) π) :
    Monotone (spectralAverage π G) := by
  intro eigenvalues η h
  apply integral_mono (hi eigenvalues) (hi η)
  intro U
  exact hG (spectralMatrix_positiveSemidefinite U eigenvalues) (spectralMatrix_positiveSemidefinite U η)
    (spectralMatrix_monotone U h)

end ResearchMain.WishartBlocks
