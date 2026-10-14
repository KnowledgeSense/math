import MainTheorems.WishartBlocks.SpectralLaw.OrthogonalHaar
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace ResearchMain.WishartBlocks

open MeasureTheory Matrix
open scoped MatrixOrder

noncomputable def clampedSpectralMatrix {n : ℕ} (δ : ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (lam : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal (fun i => max δ (lam i)) *
    (U : Matrix (Fin n) (Fin n) ℝ).transpose

theorem clampedSpectralMatrix_posDef {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (lam : Fin n → ℝ) :
    (clampedSpectralMatrix δ U lam).PosDef := by
  have hd : (Matrix.diagonal (fun i => max δ (lam i))).PosDef :=
    Matrix.PosDef.diagonal fun i => hδ.trans_le (le_max_left _ _)
  have hu : IsUnit (U : Matrix (Fin n) (Fin n) ℝ) := (Unitary.toUnits U).isUnit
  simpa only [clampedSpectralMatrix, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hd.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hu)

theorem clampedSpectralMatrix_monotone {n : ℕ} (δ : ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : Monotone (clampedSpectralMatrix δ U) := by
  intro lam η hlamη
  change (clampedSpectralMatrix δ U η - clampedSpectralMatrix δ U lam).PosSemidef
  have hd : (Matrix.diagonal (fun i => max δ (η i) - max δ (lam i))).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i => sub_nonneg.mpr (max_le_max le_rfl (hlamη i))
  have h := hd.mul_mul_conjTranspose_same (U : Matrix (Fin n) (Fin n) ℝ)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.diagonal_sub,
    Matrix.mul_sub, Matrix.sub_mul, clampedSpectralMatrix] using h

noncomputable def clampedSpectralAverage {n : ℕ} (δ : ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ → ℝ) (lam : Fin n → ℝ) : ℝ :=
  ∫ U, G (clampedSpectralMatrix δ U lam) ∂orthogonalHaar n

theorem clampedSpectralAverage_continuous {n : ℕ} (δ : ℝ)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : Continuous G) :
    Continuous (clampedSpectralAverage δ G) := by
  change Continuous (fun lam : Fin n → ℝ =>
    ∫ U, G (clampedSpectralMatrix δ U lam) ∂orthogonalHaar n)
  have hc : Continuous (fun z : (Fin n → ℝ) × Matrix.orthogonalGroup (Fin n) ℝ =>
      G (clampedSpectralMatrix δ z.2 z.1)) := by
    apply hG.comp
    unfold clampedSpectralMatrix
    fun_prop
  simpa only [setIntegral_univ] using
    continuous_parametric_integral_of_continuous (μ := orthogonalHaar n)
      (f := fun lam U => G (clampedSpectralMatrix δ U lam)) hc isCompact_univ

theorem clampedSpectral_integrable {n : ℕ} (δ : ℝ)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : Continuous G) (lam : Fin n → ℝ) :
    Integrable (fun U => G (clampedSpectralMatrix δ U lam)) (orthogonalHaar n) := by
  have hc : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      G (clampedSpectralMatrix δ U lam)) := by
    apply hG.comp
    unfold clampedSpectralMatrix
    fun_prop
  simpa only [IntegrableOn, Measure.restrict_univ] using
    hc.continuousOn.integrableOn_compact (μ := orthogonalHaar n) isCompact_univ

theorem clampedSpectralAverage_nonneg {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (hG : ∀ W, W.PosDef → 0 ≤ G W) (lam : Fin n → ℝ) :
    0 ≤ clampedSpectralAverage δ G lam := by
  exact integral_nonneg fun U => hG _ (clampedSpectralMatrix_posDef hδ U lam)

theorem clampedSpectralAverage_monotone {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hcG : Continuous G)
    (hG : MonotoneOn G {W | W.PosDef}) : Monotone (clampedSpectralAverage δ G) := by
  intro lam η hlamη
  exact integral_mono (clampedSpectral_integrable δ hcG lam)
    (clampedSpectral_integrable δ hcG η) fun U => hG
      (clampedSpectralMatrix_posDef hδ U lam) (clampedSpectralMatrix_posDef hδ U η)
      (clampedSpectralMatrix_monotone δ U hlamη)

end ResearchMain.WishartBlocks
