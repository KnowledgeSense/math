import MainTheorems.AHOConstants.RealProjections
import MainTheorems.AHOConstants.CounterexampleGeometry

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

def coordinateVector (j : Fin 3) : Fin 3 → ℝ := fun i => if i = j then 1 else 0

theorem coordinateVector_norm (j : Fin 3) :
    (∑ i, coordinateVector j i ^ 2) = 1 := by simp [coordinateVector]

theorem coordinateVectors_orthogonal {i j : Fin 3} (hij : i ≠ j) :
    (∑ t, coordinateVector i t * coordinateVector j t) = 0 := by
  simp [coordinateVector, Ne.symm hij]

noncomputable def counterexampleA (ε z : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ε • realProjection (smallEigenvector z) + realProjection (largeEigenvector z)

noncomputable def counterexampleB (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ε • realProjection (coordinateVector 0) + realProjection (coordinateVector 2)

theorem counterexampleA_realEntries (ε z : ℝ) :
    ∀ i j, (counterexampleA ε z i j).im = 0 := by
  intro i j
  simp [counterexampleA, realProjection, rankOne, realVector,
    Complex.mul_im]

theorem counterexampleB_realEntries (ε : ℝ) :
    ∀ i j, (counterexampleB ε i j).im = 0 := by
  intro i j
  simp [counterexampleB, realProjection, rankOne, realVector,
    Complex.mul_im]

theorem counterexampleA_posSemidef {ε : ℝ} (hε : 0 ≤ ε) (z : ℝ) :
    (counterexampleA ε z).PosSemidef :=
  ((realProjection_posSemidef (smallEigenvector z)).smul hε).add
    (realProjection_posSemidef (largeEigenvector z))

theorem counterexampleB_posSemidef {ε : ℝ} (hε : 0 ≤ ε) :
    (counterexampleB ε).PosSemidef :=
  ((realProjection_posSemidef (coordinateVector 0)).smul hε).add
    (realProjection_posSemidef (coordinateVector 2))

theorem counterexampleA_power {ε r : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hr : 0 < r) (z : ℝ) :
    spectralPower (counterexampleA ε z) r =
      ε ^ r • realProjection (smallEigenvector z) + realProjection (largeEigenvector z) :=
  twoProjection_spectralPower (realProjection_posSemidef _) (realProjection_posSemidef _)
    (realProjection_idempotent (smallEigenvector_norm z))
    (realProjection_idempotent (largeEigenvector_norm z))
    (realProjection_orthogonal (eigenvectors_orthogonal z)) hε₀ hε₁ hr

theorem counterexampleB_power {ε r : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hr : 0 < r) : spectralPower (counterexampleB ε) r =
      ε ^ r • realProjection (coordinateVector 0) + realProjection (coordinateVector 2) :=
  twoProjection_spectralPower (realProjection_posSemidef _) (realProjection_posSemidef _)
    (realProjection_idempotent (coordinateVector_norm 0))
    (realProjection_idempotent (coordinateVector_norm 2))
    (realProjection_orthogonal (coordinateVectors_orthogonal (by decide : (0 : Fin 3) ≠ 2)))
    hε₀ hε₁ hr

end ResearchMain.AHOConstants
