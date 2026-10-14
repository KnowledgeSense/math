import MainTheorems.WishartBlocks.SpectralLaw.ClampedAverages
import MainTheorems.WishartBlocks.SpectralLaw.SpectralAverage
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace ResearchMain.WishartBlocks

open MeasureTheory
open scoped BigOperators MatrixOrder

theorem clamped_composition_continuous {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : ContinuousOn G {W | W.PosDef}) :
    Continuous (fun p : (Fin n → ℝ) × Matrix.orthogonalGroup (Fin n) ℝ =>
      G (clampedSpectralMatrix δ p.2 p.1)) := by
  apply hG.comp_continuous
  · unfold clampedSpectralMatrix
    fun_prop
  · intro p
    exact clampedSpectralMatrix_posDef hδ p.2 p.1

theorem clamped_average_continuousOn_posDef {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : ContinuousOn G {W | W.PosDef}) :
    Continuous (clampedSpectralAverage δ G) := by
  change Continuous (fun lam : Fin n → ℝ =>
    ∫ U, G (clampedSpectralMatrix δ U lam) ∂orthogonalHaar n)
  simpa only [setIntegral_univ] using
    continuous_parametric_integral_of_continuous (μ := orthogonalHaar n)
      (f := fun lam U => G (clampedSpectralMatrix δ U lam))
      (clamped_composition_continuous hδ hG) isCompact_univ

theorem clamped_integrableOn_posDef {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : ContinuousOn G {W | W.PosDef})
    (lam : Fin n → ℝ) :
    Integrable (fun U => G (clampedSpectralMatrix δ U lam)) (orthogonalHaar n) := by
  have hc : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      G (clampedSpectralMatrix δ U lam)) :=
    (clamped_composition_continuous hδ hG).comp
      (show Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ => (lam, U)) from
        continuous_const.prodMk continuous_id)
  simpa only [Function.comp_apply, IntegrableOn, Measure.restrict_univ] using
    hc.continuousOn.integrableOn_compact (μ := orthogonalHaar n) isCompact_univ

theorem clamped_average_monotoneOn_posDef {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hcG : ContinuousOn G {W | W.PosDef})
    (hG : MonotoneOn G {W | W.PosDef}) : Monotone (clampedSpectralAverage δ G) := by
  intro lam η hlamη
  exact integral_mono (clamped_integrableOn_posDef hδ hcG lam)
    (clamped_integrableOn_posDef hδ hcG η) fun U => hG
      (clampedSpectralMatrix_posDef hδ U lam) (clampedSpectralMatrix_posDef hδ U η)
      (clampedSpectralMatrix_monotone δ U hlamη)

theorem clamped_average_eq_spectralAverage {n : ℕ} (δ : ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ → ℝ) {lam : Fin n → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hδ : ∀ i, δ ≤ lam i) :
    clampedSpectralAverage δ G lam = orthogonalSpectralAverage G lam := by
  have hp : positiveCoordinates lam = lam := by
    funext i
    exact max_eq_right (hlam i)
  have hm : (fun i => max δ (lam i)) = lam := by
    funext i
    exact max_eq_right (hδ i)
  unfold clampedSpectralAverage orthogonalSpectralAverage orthogonalAverage
  simp only [clampedSpectralMatrix, matrixCongruence, hm, hp]

noncomputable def clampedDeterminant {n : ℕ} (δ ν : ℝ) (lam : Fin n → ℝ) : ℝ :=
  (∏ i : Fin n, max δ (lam i)) ^ ν

theorem clampedDeterminant_nonneg {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (ν : ℝ) (lam : Fin n → ℝ) : 0 ≤ clampedDeterminant δ ν lam :=
  (Real.rpow_pos_of_pos (Finset.prod_pos fun _i _ =>
    hδ.trans_le (le_max_left _ _)) _).le

theorem clampedDeterminant_continuous {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (ν : ℝ) :
    Continuous (clampedDeterminant (n := n) δ ν) := by
  unfold clampedDeterminant
  apply Continuous.rpow_const (by fun_prop)
  intro lam
  exact Or.inl (Finset.prod_pos fun i _ => hδ.trans_le (le_max_left _ _)).ne'

theorem clampedDeterminant_monotone {n : ℕ} {δ ν : ℝ} (hδ : 0 < δ) (hν : 0 ≤ ν) :
    Monotone (clampedDeterminant (n := n) δ ν) := by
  intro lam η hlamη
  apply Real.rpow_le_rpow
  · exact Finset.prod_nonneg fun i _ => (hδ.trans_le (le_max_left _ _)).le
  · exact Finset.prod_le_prod₀ (fun _i _ => (hδ.trans_le (le_max_left _ _)).le)
      (fun i _ => max_le_max le_rfl (hlamη i))
  · exact hν

end ResearchMain.WishartBlocks
