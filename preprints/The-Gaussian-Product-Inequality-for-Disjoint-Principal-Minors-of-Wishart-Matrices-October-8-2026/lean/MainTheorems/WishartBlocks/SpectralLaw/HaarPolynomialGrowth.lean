import MainTheorems.WishartBlocks.SpectralLaw.ClampedPositiveDomain
import MainTheorems.WishartBlocks.SpectralLaw.SpectralIntegral
import MainTheorems.WishartBlocks.NoncentralPolynomialMoments

namespace ResearchMain.WishartBlocks

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise MatrixOrder

theorem isotropic_pd_growth_integrable {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) {G : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (hG : Measurable G) {C β : ℝ} (hC : 0 ≤ C)
    (hb : ∀ W, W.PosDef → ‖G W‖ ≤ C * (1 + ‖W‖) ^ β) :
    Integrable G (bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  let k := ⌈β⌉₊
  apply ((bartlett_polynomial_integrable hα 1 k).const_mul C).mono' hG.aestronglyMeasurable
  filter_upwards [bartlettLaw_positiveDefinite hα Matrix.PosDef.one] with W hW
  calc
    ‖G W‖ ≤ C * (1 + ‖W‖) ^ β := hb W hW
    _ ≤ C * (1 + ‖W‖) ^ k := by
      rw [← Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg W]) (Nat.le_ceil β)) hC

theorem isotropic_pd_determinant_growth_integrable {n : ℕ} {α ν : ℝ}
    (hα : (n : ℝ) - 1 < α) (hν : 0 ≤ ν)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : Measurable G)
    {C β : ℝ} (hC : 0 ≤ C)
    (hb : ∀ W, W.PosDef → ‖G W‖ ≤ C * (1 + ‖W‖) ^ β) :
    Integrable (fun W => W.det ^ ν * G W)
      (bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  let D : ℝ := Fintype.card (Equiv.Perm (Fin n))
  have hD : 0 ≤ D := Nat.cast_nonneg _
  apply isotropic_pd_growth_integrable hα (by fun_prop)
    (C := D ^ ν * C) (β := n * ν + β) (mul_nonneg (Real.rpow_nonneg hD _) hC)
  intro W hW
  have hd : W.det ≤ D * (1 + ‖W‖) ^ n := by
    have h := determinant_entry_bound W (fun i j =>
      (Matrix.norm_entry_le_entrywise_sup_norm W).trans
        (show ‖W‖ ≤ 1 + ‖W‖ by linarith))
    simpa only [Real.norm_of_nonneg hW.det_pos.le, D] using h
  rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hW.det_pos.le _)]
  calc
    W.det ^ ν * ‖G W‖ ≤ (D * (1 + ‖W‖) ^ n) ^ ν * (C * (1 + ‖W‖) ^ β) :=
      mul_le_mul (Real.rpow_le_rpow hW.det_pos.le hd hν) (hb W hW) (norm_nonneg _)
        (Real.rpow_nonneg (mul_nonneg hD (by positivity)) _)
    _ = _ := by
      rw [Real.mul_rpow hD (by positivity),
        ← Real.rpow_natCast_mul (by positivity) n ν, Real.rpow_add (by positivity)]
      ring

theorem orthogonal_diagonal_entry_bound {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) {η : Fin n → ℝ} (hη : ∀ i, 0 ≤ η i)
    (i j : Fin n) :
    ‖((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal η *
        (U : Matrix (Fin n) (Fin n) ℝ).transpose) i j‖ ≤ ∑ k, η k := by
  change ‖∑ k, ((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal η) i k *
    (U : Matrix (Fin n) (Fin n) ℝ).transpose k j‖ ≤ _
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  have hi := entry_norm_bound_of_unitary U.property i k
  have hj := entry_norm_bound_of_unitary U.property j k
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (hη k)]
  calc
    ‖(U : Matrix (Fin n) (Fin n) ℝ) i k‖ * η k *
        ‖(U : Matrix (Fin n) (Fin n) ℝ) j k‖ ≤ 1 * η k * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hi (hη k)) hj (norm_nonneg _)
        (by simpa only [one_mul] using hη k)
    _ = _ := by ring

theorem clamped_sorted_norm_bound {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.PosSemidef) :
    1 + ‖clampedSpectralMatrix δ U (sortedEigenvalues n W)‖ ≤
      (1 + n) * (1 + ‖W‖) := by
  have hn : ‖clampedSpectralMatrix δ U (sortedEigenvalues n W)‖ ≤ n + W.trace := by
    apply (Matrix.norm_le_iff (show 0 ≤ (n : ℝ) + W.trace from
      add_nonneg (Nat.cast_nonneg _) hW.trace_nonneg)).mpr
    intro i j
    refine (orthogonal_diagonal_entry_bound U
      (fun k => (hδ.trans_le (le_max_left _ _)).le) i j).trans ?_
    calc
      (∑ k : Fin n, max δ (sortedEigenvalues n W k)) ≤
          ∑ k : Fin n, (1 + sortedEigenvalues n W k) := by
        apply Finset.sum_le_sum
        intro k _
        exact max_le (hδ1.trans (le_add_of_nonneg_right (sortedEigenvalues_nonneg hW k)))
          (le_add_of_nonneg_left zero_le_one)
      _ = n + W.trace := by
        rw [Finset.sum_add_distrib, ← sortedEigenvalues_trace hW.isHermitian]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have ht : W.trace ≤ n * ‖W‖ := by
    calc
      W.trace = ∑ i : Fin n, W i i := rfl
      _ ≤ ∑ _ : Fin n, ‖W‖ := Finset.sum_le_sum fun i _ =>
        (le_abs_self _).trans (Matrix.norm_entry_le_entrywise_sup_norm W)
      _ = n * ‖W‖ := by simp
  nlinarith [norm_nonneg W]

theorem clamped_sorted_average_growth {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : ContinuousOn G {W | W.PosDef})
    {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    (hb : ∀ W, W.PosDef → ‖G W‖ ≤ C * (1 + ‖W‖) ^ k)
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.PosSemidef) :
    ‖clampedSpectralAverage δ G (sortedEigenvalues n W)‖ ≤
      C * (1 + n) ^ k * (1 + ‖W‖) ^ k := by
  have hi := clamped_integrableOn_posDef hδ hG (sortedEigenvalues n W)
  refine (norm_integral_le_integral_norm _).trans ?_
  have hc : Integrable (fun _ : Matrix.orthogonalGroup (Fin n) ℝ =>
      C * (1 + n) ^ k * (1 + ‖W‖) ^ k) (orthogonalHaar n) := integrable_const _
  have h := integral_mono hi.norm hc (fun U => by
    calc
      ‖G (clampedSpectralMatrix δ U (sortedEigenvalues n W))‖ ≤
          C * (1 + ‖clampedSpectralMatrix δ U (sortedEigenvalues n W)‖) ^ k :=
        hb _ (clampedSpectralMatrix_posDef hδ U _)
      _ ≤ C * ((1 + n) * (1 + ‖W‖)) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (clamped_sorted_norm_bound hδ hδ1 U hW) k) hC
      _ = _ := by rw [mul_pow]; ring)
  simpa only [integral_const, probReal_univ, one_smul] using h

theorem clamped_average_isotropic_integrable {n : ℕ} {α δ : ℝ}
    (hα : (n : ℝ) - 1 < α) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : ContinuousOn G {W | W.PosDef})
    {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    (hb : ∀ W, W.PosDef → ‖G W‖ ≤ C * (1 + ‖W‖) ^ k) :
    Integrable (clampedSpectralAverage δ G) (isotropicEigenvalueLaw n α) := by
  unfold isotropicEigenvalueLaw
  apply (integrable_map_measure
    (clamped_average_continuousOn_posDef hδ hG).measurable.aestronglyMeasurable
    (measurable_sortedEigenvalues n).aemeasurable).mpr
  apply ((bartlett_polynomial_integrable hα 1 k).const_mul (C * (1 + n) ^ k)).mono'
    ((clamped_average_continuousOn_posDef hδ hG).comp
      (continuous_sortedEigenvalues n)).measurable.aestronglyMeasurable
  filter_upwards [bartlettLaw_positiveDefinite hα Matrix.PosDef.one] with W hW
  exact clamped_sorted_average_growth hδ hδ1 hG hC k hb hW.posSemidef

end ResearchMain.WishartBlocks
