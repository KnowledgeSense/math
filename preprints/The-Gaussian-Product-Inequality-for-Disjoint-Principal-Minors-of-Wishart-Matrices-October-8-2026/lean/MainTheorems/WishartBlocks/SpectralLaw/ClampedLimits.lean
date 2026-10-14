import MainTheorems.WishartBlocks.SpectralLaw.WeightedClampedAverages
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace ResearchMain.WishartBlocks

open MeasureTheory Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise

noncomputable def clampScale (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)

theorem clampScale_pos (m : ℕ) : 0 < clampScale m := by
  unfold clampScale
  positivity

theorem clampScale_le_one (m : ℕ) : clampScale m ≤ 1 := by
  unfold clampScale
  simpa only [div_one] using
    (one_div_le_one_div_of_le (a := (1 : ℝ)) zero_lt_one
      (show 1 ≤ (m : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) m]))

theorem clampScale_tendsto : Tendsto clampScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem clamped_average_tendsto {n : ℕ} {I : Type*} {l : Filter I}
    {δ : I → ℝ} (hδ : Tendsto δ l (𝓝 0))
    (G : Matrix (Fin n) (Fin n) ℝ → ℝ) {lam : Fin n → ℝ} (hlam : ∀ i, 0 < lam i) :
    Tendsto (fun t => clampedSpectralAverage (δ t) G lam) l
      (𝓝 (orthogonalSpectralAverage G lam)) := by
  have he : ∀ᶠ t in l, ∀ i, δ t ≤ lam i :=
    Filter.eventually_all.mpr fun i => hδ.eventually (eventually_le_nhds (hlam i))
  apply (tendsto_const_nhds : Tendsto
    (fun _ : I => orthogonalSpectralAverage G lam) l _).congr'
  filter_upwards [he] with t ht
  exact (clamped_average_eq_spectralAverage (δ t) G (fun i => (hlam i).le) ht).symm

theorem clamped_isotropic_integrals_tendsto {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) {G : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (hmeas : Measurable G) (hG : ContinuousOn G {W | W.PosDef})
    {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    (hb : ∀ W, W.PosDef → ‖G W‖ ≤ C * (1 + ‖W‖) ^ k) :
    Tendsto (fun m => ∫ lam, clampedSpectralAverage (clampScale m) G lam
        ∂isotropicEigenvalueLaw n α) atTop (𝓝 (∫ W, G W ∂bartlettLaw α 1)) := by
  have hiG : Integrable G (bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ)) :=
    isotropic_pd_growth_integrable hα hmeas hC (β := (k : ℝ))
      (fun W hW => by simpa only [Real.rpow_natCast] using hb W hW)
  have he (m : ℕ) :
      (∫ lam, clampedSpectralAverage (clampScale m) G lam ∂isotropicEigenvalueLaw n α) =
        ∫ W, clampedSpectralAverage (clampScale m) G (sortedEigenvalues n W)
          ∂bartlettLaw α 1 := by
    exact integral_map (measurable_sortedEigenvalues n).aemeasurable
      (clamped_average_continuousOn_posDef (clampScale_pos m) hG).measurable.aestronglyMeasurable
  simp_rw [he]
  rw [← bartlettLaw_isotropic_integral_orthogonalAverage hα hmeas hiG]
  apply tendsto_integral_of_dominated_convergence
    (fun W : Matrix (Fin n) (Fin n) ℝ => C * (1 + n) ^ k * (1 + ‖W‖) ^ k)
  · intro m
    exact ((clamped_average_continuousOn_posDef (clampScale_pos m) hG).comp
      (continuous_sortedEigenvalues n)).measurable.aestronglyMeasurable
  · exact (bartlett_polynomial_integrable hα 1 k).const_mul _
  · intro m
    filter_upwards [bartlettLaw_positiveDefinite hα Matrix.PosDef.one] with W hW
    exact clamped_sorted_average_growth (clampScale_pos m) (clampScale_le_one m)
      hG hC k hb hW.posSemidef
  · filter_upwards [bartlettLaw_positiveDefinite hα Matrix.PosDef.one] with W hW
    rw [orthogonalAverage_eq_sortedSpectralAverage G hW.posSemidef]
    exact clamped_average_tendsto clampScale_tendsto G (sortedEigenvalues_pos hW)

theorem clamped_real_growth_integrals_tendsto {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) {G : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (hmeas : Measurable G) (hG : ContinuousOn G {W | W.PosDef})
    {C β : ℝ} (hC : 0 ≤ C)
    (hb : ∀ W, W.PosDef → ‖G W‖ ≤ C * (1 + ‖W‖) ^ β) :
    Tendsto (fun m => ∫ lam, clampedSpectralAverage (clampScale m) G lam
        ∂isotropicEigenvalueLaw n α) atTop (𝓝 (∫ W, G W ∂bartlettLaw α 1)) := by
  apply clamped_isotropic_integrals_tendsto hα hmeas hG hC ⌈β⌉₊
  intro W hW
  refine (hb W hW).trans ?_
  rw [← Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg W]) (Nat.le_ceil β)) hC

theorem clamped_weighted_integrals_tendsto {n : ℕ} {α ν : ℝ}
    (hα : (n : ℝ) - 1 < α) (hν : 0 ≤ ν)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (hmeas : Measurable G) (hG : ContinuousOn G {W | W.PosDef})
    {C β : ℝ} (hC : 0 ≤ C)
    (hb : ∀ W, W.PosDef → ‖G W‖ ≤ C * (1 + ‖W‖) ^ β) :
    Tendsto (fun m => ∫ lam, clampedDeterminant (clampScale m) ν lam *
        clampedSpectralAverage (clampScale m) G lam ∂isotropicEigenvalueLaw n α)
      atTop (𝓝 (∫ W, W.det ^ ν * G W ∂bartlettLaw α 1)) := by
  have hd : Continuous (fun W : Matrix (Fin n) (Fin n) ℝ => W.det ^ ν) :=
    (by fun_prop : Continuous (fun W : Matrix (Fin n) (Fin n) ℝ => W.det)).rpow_const
      (fun _ => Or.inr hν)
  have hi := clamped_real_growth_integrals_tendsto hα
    (G := fun W => W.det ^ ν * G W) (hd.measurable.mul hmeas)
    (hd.continuousOn.mul hG)
    (C := (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ^ ν * C)
    (β := (n : ℝ) * ν + β)
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hC)
    (pd_determinant_weight_growth hν hC hb)
  simpa only [clamped_average_determinant_weight] using hi

end ResearchMain.WishartBlocks
