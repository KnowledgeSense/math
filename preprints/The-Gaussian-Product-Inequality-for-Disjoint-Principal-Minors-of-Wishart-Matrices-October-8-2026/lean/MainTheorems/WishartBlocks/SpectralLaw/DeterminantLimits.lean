import MainTheorems.WishartBlocks.SpectralLaw.ClampedLimits

namespace ResearchMain.WishartBlocks

open MeasureTheory Filter
open scoped Topology Matrix.Norms.Elementwise

theorem clamped_average_nonnegOn_posDef {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (hG : ∀ W, W.PosDef → 0 ≤ G W) (lam : Fin n → ℝ) :
    0 ≤ clampedSpectralAverage δ G lam :=
  integral_nonneg (fun U => hG _ (clampedSpectralMatrix_posDef hδ U lam))

@[simp] theorem clamped_average_one {n : ℕ} (δ : ℝ) (lam : Fin n → ℝ) :
    clampedSpectralAverage δ (fun _ => (1 : ℝ)) lam = 1 := by
  simp only [clampedSpectralAverage, integral_const, probReal_univ, one_smul]

theorem clamped_determinant_integrals_tendsto {n : ℕ} {α ν : ℝ}
    (hα : (n : ℝ) - 1 < α) (hν : 0 ≤ ν) :
    Tendsto (fun m => ∫ lam, clampedDeterminant (clampScale m) ν lam
        ∂isotropicEigenvalueLaw n α) atTop
      (𝓝 (∫ W : Matrix (Fin n) (Fin n) ℝ, W.det ^ ν ∂bartlettLaw α 1)) := by
  have h := clamped_weighted_integrals_tendsto hα hν (G := fun _ => (1 : ℝ))
    measurable_const continuousOn_const (C := 1) (β := 0) zero_le_one
    (fun _ _ => by simp)
  simpa only [clamped_average_one, mul_one] using h

end ResearchMain.WishartBlocks
