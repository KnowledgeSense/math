import MainTheorems.WishartBlocks.SpectralLaw.CholeskyCoordinates
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.LinearAlgebra.Matrix.Hermitian

namespace ResearchMain.WishartBlocks

noncomputable def symmetricEntry {n : ℕ} (i j : Fin n) :
    (LowerIndex n → ℝ) →L[ℝ] ℝ :=
  if h : j ≤ i then ContinuousLinearMap.proj ⟨toLex (i, j), h⟩
    else ContinuousLinearMap.proj ⟨toLex (j, i), le_of_not_ge h⟩

noncomputable def symmetricMatrix {n : ℕ} (x : LowerIndex n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => symmetricEntry i j x

def symmetricCoordinates {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) :
    LowerIndex n → ℝ := fun e => W e.val.1 e.val.2

theorem symmetricMatrix_isHermitian {n : ℕ} (x : LowerIndex n → ℝ) :
    (symmetricMatrix x).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  unfold symmetricMatrix symmetricEntry
  by_cases hji : j ≤ i
  · by_cases hij : i ≤ j
    · have he : i = j := le_antisymm hij hji
      subst j
      simp only [le_refl, dite_true]
    · simp only [hji, hij, dite_true, dite_false]
  · have hij : i ≤ j := le_of_not_ge hji
    simp only [hji, hij, dite_true, dite_false]

@[simp] theorem symmetricCoordinates_symmetricMatrix {n : ℕ} (x : LowerIndex n → ℝ) :
    symmetricCoordinates (symmetricMatrix x) = x := by
  funext e
  simp only [symmetricCoordinates, symmetricMatrix, symmetricEntry,
    e.property, dite_true, ContinuousLinearMap.proj_apply]
  congr 1

theorem symmetricMatrix_symmetricCoordinates {n : ℕ}
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.IsHermitian) :
    symmetricMatrix (symmetricCoordinates W) = W := by
  ext i j
  unfold symmetricMatrix symmetricEntry
  split_ifs with h
  · rfl
  · change W j i = W i j
    simpa only [star_trivial] using hW.apply i j

@[fun_prop] theorem symmetricMatrix_continuous (n : ℕ) :
    Continuous (symmetricMatrix (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (symmetricEntry i j).continuous

theorem symmetricMatrix_choleskyCoordinates {n : ℕ} (x : LowerIndex n → ℝ) :
    symmetricMatrix (choleskyCoordinates x) = lowerMatrix x * (lowerMatrix x).transpose := by
  have h := Matrix.isHermitian_mul_conjTranspose_self (lowerMatrix x)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact symmetricMatrix_symmetricCoordinates h

end ResearchMain.WishartBlocks
