import MainTheorems.WishartBlocks.GaussianDeterminantShift
import MainTheorems.WishartBlocks.ShiftedDeterminantMoments

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder InnerProductSpace

theorem rankOne_shifted_determinant_monotone {p : ℕ} {q b : ℝ}
    (hq : (p : ℝ) < q) (hb : 0 ≤ b)
    {S K : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hK : K.PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) :
    MonotoneOn
      (fun θ => ∫ W : Matrix (Fin p) (Fin p) ℝ, (W + K).det ^ b
        ∂(oneRowWishartLaw q S (Real.sqrt θ • v))) (Set.Ici 0) := by
  let : IsProbabilityMeasure (bartlettLaw (q - 1) S) :=
    bartlett_law_probability (by linarith) S
  let : MeasurableAdd₂ (Matrix (Fin p) (Fin p) ℝ) :=
    inferInstanceAs (MeasurableAdd₂ (Fin p → Fin p → ℝ))
  have hg : Measurable (fun W : Matrix (Fin p) (Fin p) ℝ => (W + K).det ^ b) := by
    fun_prop
  let μ := bartlettLaw (q - 1) S
  let γ := stdGaussian (EuclideanSpace ℝ (Fin p))
  let f := fun θ (wz : Matrix (Fin p) (Fin p) ℝ × EuclideanSpace ℝ (Fin p)) =>
    (oneRowWishartValue S (Real.sqrt θ • v) wz + K).det ^ b
  have hi : ∀ θ, Integrable (f θ) (μ.prod γ) := by
    intro θ
    have h := oneRowWishart_shifted_determinant_integrable hq hb hS (Real.sqrt θ • v) K
    unfold oneRowWishartLaw at h
    exact (integrable_map_measure hg.aestronglyMeasurable
      (measurable_oneRowWishartValue S (Real.sqrt θ • v)).aemeasurable).mp h
  have he : ∀ θ,
      (∫ W : Matrix (Fin p) (Fin p) ℝ, (W + K).det ^ b
        ∂(oneRowWishartLaw q S (Real.sqrt θ • v))) =
      ∫ V, ∫ z, ((V + K) + gaussianMeanGram S (Real.sqrt θ • v) z).det ^ b ∂γ ∂μ := by
    intro θ
    unfold oneRowWishartLaw
    rw [integral_map (measurable_oneRowWishartValue S (Real.sqrt θ • v)).aemeasurable
      hg.aestronglyMeasurable, integral_prod _ (hi θ)]
    simp only [f, oneRowWishartValue, add_assoc, add_comm, μ, γ]
  intro θ hθ η hη hθη
  dsimp only
  rw [he θ, he η]
  apply integral_mono_ae
    (by simpa only [f, oneRowWishartValue, add_assoc, add_left_comm, add_comm]
      using (hi θ).integral_prod_left)
    (by simpa only [f, oneRowWishartValue, add_assoc, add_left_comm, add_comm]
      using (hi η).integral_prod_left)
  filter_upwards [bartlettLaw_positiveDefinite (by linarith : (p : ℝ) - 1 < q - 1) hS]
    with V hV
  exact determinant_gaussian_shift_ray_monotone hb (hV.add_posSemidef hK) hS v hθ hη hθη

theorem rankOne_determinant_monotone {p : ℕ} {q b : ℝ}
    (hq : (p : ℝ) < q) (hb : 0 ≤ b) {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (v : EuclideanSpace ℝ (Fin p)) :
    MonotoneOn
      (fun θ => ∫ W : Matrix (Fin p) (Fin p) ℝ, W.det ^ b
        ∂(oneRowWishartLaw q S (Real.sqrt θ • v))) (Set.Ici 0) := by
  simpa only [add_zero] using rankOne_shifted_determinant_monotone hq hb hS
    (Matrix.PosSemidef.zero : (0 : Matrix (Fin p) (Fin p) ℝ).PosSemidef) v

end ResearchMain.WishartBlocks
