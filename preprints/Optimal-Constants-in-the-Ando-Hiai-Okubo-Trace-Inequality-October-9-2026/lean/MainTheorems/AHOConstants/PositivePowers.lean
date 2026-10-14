import MainTheorems.AHOConstants.ComplexPowers

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem complexPower_isUnit {A : Matrix I I ℂ} (hA : A.PosDef) (z : ℂ) :
    IsUnit (complexPower hA z) := by
  refine ⟨⟨complexPower hA z, complexPower hA (-z), ?_, ?_⟩, rfl⟩
  · rw [← complexPower_add, add_neg_cancel, complexPower_zero]
  · rw [← complexPower_add, neg_add_cancel, complexPower_zero]

theorem spectralPower_isUnit {A : Matrix I I ℂ} (hA : A.PosDef) (r : ℝ) :
    IsUnit (spectralPower A r) := by
  rw [← complexPower_real hA r]
  exact complexPower_isUnit hA r

theorem spectralPower_posDef {A : Matrix I I ℂ} (hA : A.PosDef) (r : ℝ) :
    (spectralPower A r).PosDef :=
  (spectralPower_positiveSemidefinite A r).posDef_iff_isUnit.mpr (spectralPower_isUnit hA r)

theorem spectralPower_add_real {A : Matrix I I ℂ} (hA : A.PosDef) (r t : ℝ) :
    spectralPower A (r + t) = spectralPower A r * spectralPower A t := by
  rw [← complexPower_real hA (r + t), ← complexPower_real hA r, ← complexPower_real hA t]
  simpa only [Complex.ofReal_add] using complexPower_add hA (r : ℂ) (t : ℂ)

theorem spectralPower_inverse_right {A : Matrix I I ℂ} (hA : A.PosDef) (r : ℝ) :
    spectralPower A r * spectralPower A (-r) = 1 := by
  rw [← spectralPower_add_real hA, add_neg_cancel, spectralPower_zero A hA.posSemidef]

theorem spectralPower_inverse_left {A : Matrix I I ℂ} (hA : A.PosDef) (r : ℝ) :
    spectralPower A (-r) * spectralPower A r = 1 := by
  rw [← spectralPower_add_real hA, neg_add_cancel, spectralPower_zero A hA.posSemidef]

theorem spectralPower_iterate {A : Matrix I I ℂ} (hA : A.PosDef)
    (r t : ℝ) (hr : r ≠ 0) :
    spectralPower (spectralPower A r) t = spectralPower A (r * t) :=
  CFC.rpow_rpow A r t hr hA.isStrictlyPositive

end ResearchMain.AHOConstants
