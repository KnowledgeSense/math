import MainTheorems.WishartBlocks.SpectralLaw.Weyl.SmoothGlobal
import MainTheorems.WishartBlocks.SpectralLaw.Weyl.OrderedCoverage
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace ResearchMain.WishartBlocks.Weyl

open MeasureTheory Set

noncomputable def diagonalDifferenceLinearMap {n : ℕ} (i j : Fin n) :
    (LowerIndex n → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj ⟨toLex (i, i), le_refl i⟩ -
    LinearMap.proj ⟨toLex (j, j), le_refl j⟩

theorem diagonalDifferenceLinearMap_ker_ne_top {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (diagonalDifferenceLinearMap i j).ker ≠ ⊤ := by
  classical
  intro hker
  have h : diagonalDifferenceLinearMap i j = 0 := LinearMap.ker_eq_top.mp hker
  have hdiag : (⟨toLex (i, i), le_refl i⟩ : LowerIndex n) ≠
      ⟨toLex (j, j), le_refl j⟩ := by
    intro heq
    exact hij (congrArg (fun e : LowerIndex n => e.val.1) heq)
  have hv := congrArg (fun f : (LowerIndex n → ℝ) →ₗ[ℝ] ℝ =>
    f (Pi.single ⟨toLex (i, i), le_refl i⟩ 1)) h
  simp [diagonalDifferenceLinearMap, Ne.symm hdiag] at hv

theorem diagonalCollision_volume_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    volume {z : LowerIndex n → ℝ | diagonalCoordinates z i = diagonalCoordinates z j} = 0 := by
  have hset : {z : LowerIndex n → ℝ | diagonalCoordinates z i = diagonalCoordinates z j} =
      (diagonalDifferenceLinearMap i j).ker := by
    ext z
    simp [LinearMap.mem_ker, diagonalDifferenceLinearMap, diagonalCoordinates, sub_eq_zero]
  rw [hset]
  exact Measure.addHaar_submodule volume _ (diagonalDifferenceLinearMap_ker_ne_top hij)

theorem repeatedDiagonalCoordinates_volume_zero (n : ℕ) :
    volume {z : LowerIndex n → ℝ | ¬ Function.Injective (diagonalCoordinates z)} = 0 := by
  have hnull : volume (⋃ i : Fin n, ⋃ j : Fin n, ⋃ (_ : i ≠ j),
      {z : LowerIndex n → ℝ | diagonalCoordinates z i = diagonalCoordinates z j}) = 0 :=
    measure_iUnion_null fun i => measure_iUnion_null fun j =>
      measure_iUnion_null fun hij => diagonalCollision_volume_zero hij
  apply measure_mono_null _ hnull
  intro z hz
  obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hz
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hij, heq⟩⟩⟩

theorem repeatedSpectrum_coordinates_volume_zero (n : ℕ) :
    volume {W : LowerIndex n → ℝ |
      ¬ Function.Injective (sortedEigenvalues n (symmetricMatrix W))} = 0 := by
  have himage : volume (globalSpectralCoordinates ''
      {z : LowerIndex n → ℝ | ¬ Function.Injective (diagonalCoordinates z)}) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (globalSpectralCoordinates_differentiable n).differentiableOn
      (repeatedDiagonalCoordinates_volume_zero n)
  apply measure_mono_null _ himage
  intro W hW
  obtain ⟨z, hz, hlam⟩ := symmetricCoordinates_exists_ordered_globalSpectralCoordinates W
  change ¬ Function.Injective (sortedEigenvalues n (symmetricMatrix W)) at hW
  refine ⟨z, ?_, hz⟩
  change ¬ Function.Injective (diagonalCoordinates z)
  rwa [hlam]

end ResearchMain.WishartBlocks.Weyl
