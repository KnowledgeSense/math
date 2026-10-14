import MainTheorems.WishartBlocks.SpectralLaw.Weyl.IntegralFormula
import MainTheorems.WishartBlocks.SpectralLaw.EigenvalueWeightAlgebra
import MainTheorems.WishartBlocks.SpectralLaw.EigenvalueDensityAssociation

namespace ResearchMain.WishartBlocks.Weyl

open MeasureTheory Set
open scoped ENNReal

theorem wishartCoordinateDensity_symmetricCoordinates {n : ℕ} (α : ℝ)
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.IsHermitian) :
    wishartCoordinateDensity α (symmetricCoordinates W) =
      @ite ℝ≥0∞ W.PosDef (Classical.propDecidable _)
        (ENNReal.ofReal (wishartDensityReal α W)) 0 := by
  classical
  unfold wishartCoordinateDensity
  by_cases hpd : W.PosDef
  · have hmem : symmetricCoordinates W ∈ positiveSymmetricCoordinates n := by
      change (symmetricMatrix (symmetricCoordinates W)).PosDef
      rwa [symmetricMatrix_symmetricCoordinates hW]
    rw [indicator_of_mem hmem, symmetricMatrix_symmetricCoordinates hW, ite_eq_left hpd]
  · have hmem : symmetricCoordinates W ∉ positiveSymmetricCoordinates n := by
      change ¬ (symmetricMatrix (symmetricCoordinates W)).PosDef
      rwa [symmetricMatrix_symmetricCoordinates hW]
    rw [indicator_of_notMem hmem, ite_eq_right hpd]

theorem orthogonalDiagonal_posDef_iff {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (lam : Fin n → ℝ) :
    (orthogonalDiagonal Q lam).PosDef ↔ (Matrix.diagonal lam).PosDef := by
  simpa only [orthogonalDiagonal, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.IsUnit.posDef_star_right_conjugate_iff
      (x := Matrix.diagonal lam) (Unitary.isUnit_coe (U := Q))

theorem wishartCoordinateDensity_orthogonalDiagonal {n : ℕ} (α : ℝ)
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (lam : Fin n → ℝ) :
    wishartCoordinateDensity α (symmetricCoordinates (orthogonalDiagonal Q lam)) =
      wishartCoordinateDensity α (symmetricCoordinates (Matrix.diagonal lam)) := by
  have hd : wishartDensityReal α (orthogonalDiagonal Q lam) =
      wishartDensityReal α (Matrix.diagonal lam) :=
    wishartDensityReal_orthogonal_congruence α Q (Matrix.diagonal lam)
  rw [wishartCoordinateDensity_symmetricCoordinates α (orthogonalDiagonal_isHermitian Q lam),
    wishartCoordinateDensity_symmetricCoordinates α (Matrix.isHermitian_diagonal lam),
    orthogonalDiagonal_posDef_iff, hd]

theorem wishartCoordinateDensity_diagonal_gap {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) {lam : Fin n → ℝ} (hlam : StrictMono lam) :
    ENNReal.ofReal (gapProduct lam) *
        wishartCoordinateDensity α (symmetricCoordinates (Matrix.diagonal lam)) =
      ENNReal.ofReal (wishartDensityCoefficient n α) * ENNReal.ofReal (eigenvalueWeight α lam) := by
  by_cases hp : ∀ i, 0 < lam i
  · have hpd : (Matrix.diagonal lam).PosDef := Matrix.posDef_diagonal_iff.mpr hp
    have hw : wishartCoordinateDensity α (symmetricCoordinates (Matrix.diagonal lam)) =
        ENNReal.ofReal (wishartDensityReal α (Matrix.diagonal lam)) := by
      rw [wishartCoordinateDensity_symmetricCoordinates α (Matrix.isHermitian_diagonal lam),
        ite_eq_left hpd]
    rw [hw, mul_comm (ENNReal.ofReal (gapProduct lam)),
      ← ENNReal.ofReal_mul (wishartDensityReal_pos hα hpd).le,
      wishartDensityReal_diagonal_gap α ⟨hp, hlam⟩,
      ENNReal.ofReal_mul (wishartDensityCoefficient_pos hα).le]
  · have hpd : ¬ (Matrix.diagonal lam).PosDef :=
      fun h => hp (Matrix.posDef_diagonal_iff.mp h)
    have hord : ¬ OrderedPositive lam := fun h => hp h.1
    rw [wishartCoordinateDensity_symmetricCoordinates α (Matrix.isHermitian_diagonal lam),
      ite_eq_right hpd]
    simp only [mul_zero, eigenvalueWeight, chamberWeight, hord, ite_false,
      ENNReal.ofReal_zero]

theorem coordinateOrthogonalAverageNN_densitySpectrum {n : ℕ} (α : ℝ)
    (f : (Fin n → ℝ) → ℝ≥0∞) {lam : Fin n → ℝ} (hlam : StrictMono lam) :
    coordinateOrthogonalAverageNN (fun W => wishartCoordinateDensity α W *
        f (sortedEigenvalues n (symmetricMatrix W)))
      (symmetricCoordinates (Matrix.diagonal lam)) =
        wishartCoordinateDensity α (symmetricCoordinates (Matrix.diagonal lam)) * f lam := by
  have hcoord (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
      orthogonalCongruenceLinearMap Q (symmetricCoordinates (Matrix.diagonal lam)) =
        symmetricCoordinates (orthogonalDiagonal Q lam) := by
    change symmetricCoordinates (Q.val *
      symmetricMatrix (symmetricCoordinates (Matrix.diagonal lam)) * Q.val.transpose) = _
    rw [symmetricMatrix_symmetricCoordinates (Matrix.isHermitian_diagonal _)]
    rfl
  unfold coordinateOrthogonalAverageNN
  simp_rw [hcoord, symmetricMatrix_symmetricCoordinates (orthogonalDiagonal_isHermitian _ _),
    sortedEigenvalues_orthogonalDiagonal _ hlam.monotone,
    wishartCoordinateDensity_orthogonalDiagonal]
  simp

end ResearchMain.WishartBlocks.Weyl
