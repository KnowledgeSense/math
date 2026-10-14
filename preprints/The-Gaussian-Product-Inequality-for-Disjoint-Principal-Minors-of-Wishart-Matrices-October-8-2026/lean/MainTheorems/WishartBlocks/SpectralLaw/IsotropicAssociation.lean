import MainTheorems.WishartBlocks.SpectralLaw.Weyl.IsotropicDensity
import MainTheorems.WishartBlocks.SpectralLaw.EigenvalueDensityAssociation
import MainTheorems.WishartBlocks.SpectralLaw.DeterminantLimits

namespace ResearchMain.WishartBlocks

open MeasureTheory Filter
open scoped Topology MatrixOrder Matrix.Norms.Elementwise

theorem isotropic_wishart_determinant_association {n : ℕ} {α ν : ℝ}
    (hα : (n : ℝ) - 1 < α) (hν : 0 ≤ ν)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (hmeas : Measurable G) (hcG : ContinuousOn G {W | W.PosDef})
    (hmG : MonotoneOn G {W | W.PosDef})
    (hG : ∀ W, W.PosDef → 0 ≤ G W)
    (hgrowth : ∃ C : ℝ, 0 ≤ C ∧ ∃ β : ℝ,
      ∀ W, W.PosDef → ‖G W‖ ≤ C * (1 + ‖W‖) ^ β) :
    (∫ W : Matrix (Fin n) (Fin n) ℝ, W.det ^ ν ∂bartlettLaw α 1) *
        (∫ W, G W ∂bartlettLaw α 1) ≤
      ∫ W, W.det ^ ν * G W ∂bartlettLaw α 1 := by
  obtain ⟨C, hC, β, hb⟩ := hgrowth
  obtain ⟨c, hc, hdensity⟩ := isotropicEigenvalueLaw_density hα
  have hlaw : isotropicEigenvalueLaw n α = eigenvalueDensityLaw n c α := hdensity
  let _ := bartlett_law_probability hα (1 : Matrix (Fin n) (Fin n) ℝ)
  let _ : IsProbabilityMeasure (eigenvalueDensityLaw n c α) := by
    rw [← hlaw]
    infer_instance
  have hclamp (m : ℕ) :
      (∫ lam, clampedDeterminant (clampScale m) ν lam ∂isotropicEigenvalueLaw n α) *
          (∫ lam, clampedSpectralAverage (clampScale m) G lam ∂isotropicEigenvalueLaw n α) ≤
        ∫ lam, clampedDeterminant (clampScale m) ν lam *
          clampedSpectralAverage (clampScale m) G lam ∂isotropicEigenvalueLaw n α := by
    simp only [hlaw]
    apply eigenvalueDensityLaw_association hc α
      (clampedDeterminant_continuous (clampScale_pos m) ν)
      (clamped_average_continuousOn_posDef (clampScale_pos m) hcG)
      (clampedDeterminant_nonneg (clampScale_pos m) ν)
      (clamped_average_nonnegOn_posDef (clampScale_pos m) hG)
      (clampedDeterminant_monotone (clampScale_pos m) hν)
      (clamped_average_monotoneOn_posDef (clampScale_pos m) hcG hmG)
    · rw [← hlaw]
      exact clamped_determinant_isotropic_integrable hα (clampScale_pos m)
        (clampScale_le_one m) hν
    · rw [← hlaw]
      exact clamped_average_real_growth_integrable hα (clampScale_pos m)
        (clampScale_le_one m) hcG hC hb
    · rw [← hlaw]
      exact clamped_weighted_average_isotropic_integrable hα (clampScale_pos m)
        (clampScale_le_one m) hν hcG hC hb
  exact le_of_tendsto_of_tendsto
    ((clamped_determinant_integrals_tendsto hα hν).mul
      (clamped_real_growth_integrals_tendsto hα hmeas hcG hC hb))
    (clamped_weighted_integrals_tendsto hα hν hmeas hcG hC hb)
    (Filter.Eventually.of_forall hclamp)

end ResearchMain.WishartBlocks
