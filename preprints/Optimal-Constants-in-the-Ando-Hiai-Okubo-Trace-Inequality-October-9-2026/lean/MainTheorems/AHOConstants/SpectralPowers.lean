import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def spectralPower (A : Matrix I I ℂ) (r : ℝ) : Matrix I I ℂ :=
  CFC.rpow A r

theorem spectralPower_zero (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    spectralPower A 0 = 1 := by
  exact CFC.rpow_zero A hA.nonneg

theorem spectralPower_one (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    spectralPower A 1 = A := by
  exact CFC.rpow_one A hA.nonneg

theorem spectralPower_positiveSemidefinite (A : Matrix I I ℂ) (r : ℝ) :
    (spectralPower A r).PosSemidef := by
  exact Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg

theorem spectralPower_add (A : Matrix I I ℂ) (hA : A.PosSemidef)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    spectralPower A (x + y) = spectralPower A x * spectralPower A y := by
  by_cases hxy : x + y = 0
  · have hx' : x = 0 := by linarith
    have hy' : y = 0 := by linarith
    subst x
    subst y
    simp [spectralPower_zero A hA]
  · change A ^ (x + y) = A ^ x * A ^ y
    simp only [CFC.rpow_def]
    rw [← cfc_mul _ _ A]
    apply cfc_congr
    intro z _
    exact NNReal.rpow_add' hxy z

theorem spectralPower_identity (r : ℝ) :
    spectralPower (1 : Matrix I I ℂ) r = 1 := by
  exact CFC.one_rpow

end ResearchMain.AHOConstants
