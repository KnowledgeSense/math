import MainTheorems.DiagonalSchatten.EntryPowerCoordinates
import MainTheorems.DiagonalSchatten.TwoColumnHessianSigns

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped Matrix.Norms.Elementwise

theorem two_column_second_variation_upper {p : ℝ} (hp : 2 < p)
    (X Y : Matrix (Fin 2) (Fin 2) ℝ) (hX : ∀ i j, 0 < X i j)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) :
    symmetricTraceProduct (gramVariation X Y)
        (symmetricPowerVariation ((p - 2) / 2) (gramCoordinates X) (gramVariation X Y)) ≤
      2 * compressionKernelEnergy p X Y := by
  have hp0 : p ≠ 0 := by linarith
  let B := realEntryPower p X
  let E := entryPowerDirection p X Y
  have hB : ∀ i j, 0 < B i j := fun i j => Real.rpow_pos_of_pos (hX i j) p
  have hroot : realEntryRoot p B = X := realEntryRoot_entryPower hp0 X (fun i j => (hX i j).le)
  have hY : entryRootDirection p B E = Y := entryRootDirection_entryPower hp0 X Y hX
  have hrootdet : (realEntryRoot p B).det ≠ 0 := by
    rw [hroot]
    have hd := hdet
    rw [twoByTwo_gramDet_eq_det_sq] at hd
    exact (sq_pos_iff.mp hd)
  have hsign := two_column_compressionHessian_nonpos hp B E hB hrootdet
  have hf := compressionHessian_second_variation (by linarith : 1 < p) B E hB
    (by simpa only [hroot] using hdet)
  dsimp only at hf
  rw [hroot, hY] at hf
  rw [hf] at hsign
  nlinarith

theorem two_column_second_variation_lower {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (X Y : Matrix (Fin 2) (Fin 2) ℝ) (hX : ∀ i j, 0 < X i j)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) :
    2 * compressionKernelEnergy p X Y ≤
      symmetricTraceProduct (gramVariation X Y)
        (symmetricPowerVariation ((p - 2) / 2) (gramCoordinates X) (gramVariation X Y)) := by
  have hp0 : p ≠ 0 := by linarith
  let B := realEntryPower p X
  let E := entryPowerDirection p X Y
  have hB : ∀ i j, 0 < B i j := fun i j => Real.rpow_pos_of_pos (hX i j) p
  have hroot : realEntryRoot p B = X := realEntryRoot_entryPower hp0 X (fun i j => (hX i j).le)
  have hY : entryRootDirection p B E = Y := entryRootDirection_entryPower hp0 X Y hX
  have hrootdet : (realEntryRoot p B).det ≠ 0 := by
    rw [hroot]
    have hd := hdet
    rw [twoByTwo_gramDet_eq_det_sq] at hd
    exact (sq_pos_iff.mp hd)
  have hsign := two_column_compressionHessian_nonneg hp hp2 B E hB hrootdet
  have hf := compressionHessian_second_variation hp B E hB
    (by simpa only [hroot] using hdet)
  dsimp only at hf
  rw [hroot, hY] at hf
  rw [hf] at hsign
  nlinarith

end

end ResearchMain.DiagonalSchatten
