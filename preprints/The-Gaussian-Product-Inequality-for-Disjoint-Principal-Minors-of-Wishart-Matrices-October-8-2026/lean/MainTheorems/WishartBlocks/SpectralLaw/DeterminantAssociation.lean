import MainTheorems.WishartBlocks.SpectralLaw.IsotropicAssociation
import MainTheorems.WishartBlocks.SpectralLaw.CovarianceTransport

namespace ResearchMain.WishartBlocks

open MeasureTheory
open scoped MatrixOrder Matrix.Norms.Elementwise

theorem wishart_determinant_association {n : ℕ} {α ν : ℝ}
    (hα : (n : ℝ) - 1 < α) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (hν : 0 ≤ ν) {G : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (hmeas : Measurable G) (hcG : ContinuousOn G {W | W.PosDef})
    (hmG : MonotoneOn G {W | W.PosDef})
    (hG : ∀ W, W.PosDef → 0 ≤ G W)
    (hgrowth : ∃ C : ℝ, 0 ≤ C ∧ ∃ β : ℝ,
      ∀ W, W.PosDef → ‖G W‖ ≤ C * (1 + ‖W‖) ^ β) :
    (∫ W : Matrix (Fin n) (Fin n) ℝ, W.det ^ ν ∂bartlettLaw α A) *
        (∫ W, G W ∂bartlettLaw α A) ≤
      ∫ W, W.det ^ ν * G W ∂bartlettLaw α A := by
  obtain ⟨C, hC, β, hb⟩ := hgrowth
  let H := fun W => G (matrixCongruence (choleskyFactor hA) W)
  have hHmeas : Measurable H := hmeas.comp (measurable_matrixCongruence _)
  have hHc : ContinuousOn H {W | W.PosDef} :=
    continuousOn_choleskyCongruence_response hA hcG
  have hHm : MonotoneOn H {W | W.PosDef} :=
    monotoneOn_choleskyCongruence_response hA hmG
  have hH : ∀ W, W.PosDef → 0 ≤ H W :=
    fun _ hW => hG _ (choleskyCongruence_posDef hA hW)
  have hHgrowth := choleskyCongruence_response_growth hA hC hb
  have hi := isotropic_wishart_determinant_association hα hν hHmeas hHc hHm hH hHgrowth
  have hdet : (∫ W : Matrix (Fin n) (Fin n) ℝ, W.det ^ ν ∂bartlettLaw α A) =
      A.det ^ ν * ∫ W : Matrix (Fin n) (Fin n) ℝ, W.det ^ ν ∂bartlettLaw α 1 := by
    simpa only [mul_one] using
      bartlett_weighted_integral_choleskyCongruence hα hA (ν := ν)
        (G := fun _ => (1 : ℝ)) measurable_const
  rw [hdet, bartlett_integral_choleskyCongruence hα hA hmeas,
    bartlett_weighted_integral_choleskyCongruence hα hA hmeas]
  calc
    _ = A.det ^ ν * ((∫ W : Matrix (Fin n) (Fin n) ℝ, W.det ^ ν ∂bartlettLaw α 1) *
        (∫ W, H W ∂bartlettLaw α 1)) := by dsimp [H]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hA.det_pos.le _)

end ResearchMain.WishartBlocks
