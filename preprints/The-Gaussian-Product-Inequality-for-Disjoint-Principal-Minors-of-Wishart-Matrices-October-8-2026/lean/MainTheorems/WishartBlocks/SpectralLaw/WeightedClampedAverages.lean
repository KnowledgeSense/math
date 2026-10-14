import MainTheorems.WishartBlocks.SpectralLaw.HaarPolynomialGrowth

namespace ResearchMain.WishartBlocks

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise MatrixOrder

theorem clamped_average_determinant_weight {n : ℕ} (δ ν : ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ → ℝ) (lam : Fin n → ℝ) :
    clampedSpectralAverage δ (fun W => W.det ^ ν * G W) lam =
      clampedDeterminant δ ν lam * clampedSpectralAverage δ G lam := by
  unfold clampedSpectralAverage clampedDeterminant
  change (∫ U, (matrixCongruence (U : Matrix (Fin n) (Fin n) ℝ)
      (Matrix.diagonal (fun i => max δ (lam i)))).det ^ ν *
      G (clampedSpectralMatrix δ U lam) ∂orthogonalHaar n) = _
  simp_rw [orthogonal_congruence_det, Matrix.det_diagonal]
  exact integral_const_mul _ _

theorem pd_determinant_weight_growth {n : ℕ} {ν : ℝ} (hν : 0 ≤ ν)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} {C β : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ W, W.PosDef → ‖G W‖ ≤ C * (1 + ‖W‖) ^ β) :
    ∀ W, W.PosDef → ‖W.det ^ ν * G W‖ ≤
      ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) ^ ν * C) *
        (1 + ‖W‖) ^ ((n : ℝ) * ν + β) := by
  intro W hW
  let D : ℝ := Fintype.card (Equiv.Perm (Fin n))
  have hD : 0 ≤ D := Nat.cast_nonneg _
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

theorem clamped_average_real_growth_integrable {n : ℕ} {α δ : ℝ}
    (hα : (n : ℝ) - 1 < α) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : ContinuousOn G {W | W.PosDef})
    {C β : ℝ} (hC : 0 ≤ C)
    (hb : ∀ W, W.PosDef → ‖G W‖ ≤ C * (1 + ‖W‖) ^ β) :
    Integrable (clampedSpectralAverage δ G) (isotropicEigenvalueLaw n α) := by
  apply clamped_average_isotropic_integrable hα hδ hδ1 hG hC ⌈β⌉₊
  intro W hW
  refine (hb W hW).trans ?_
  rw [← Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg W]) (Nat.le_ceil β)) hC

theorem clamped_weighted_average_isotropic_integrable {n : ℕ} {α δ ν : ℝ}
    (hα : (n : ℝ) - 1 < α) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : ContinuousOn G {W | W.PosDef})
    {C β : ℝ} (hC : 0 ≤ C)
    (hb : ∀ W, W.PosDef → ‖G W‖ ≤ C * (1 + ‖W‖) ^ β) :
    Integrable (fun lam => clampedDeterminant δ ν lam * clampedSpectralAverage δ G lam)
      (isotropicEigenvalueLaw n α) := by
  have hd : Continuous (fun W : Matrix (Fin n) (Fin n) ℝ => W.det ^ ν) :=
    (by fun_prop : Continuous (fun W : Matrix (Fin n) (Fin n) ℝ => W.det)).rpow_const
      (fun _ => Or.inr hν)
  have hg : ContinuousOn (fun W : Matrix (Fin n) (Fin n) ℝ => W.det ^ ν * G W)
      {W | W.PosDef} := hd.continuousOn.mul hG
  have hi := clamped_average_real_growth_integrable hα hδ hδ1 hg
    (C := (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ^ ν * C)
    (β := (n : ℝ) * ν + β)
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hC)
    (pd_determinant_weight_growth hν hC hb)
  have he : clampedSpectralAverage δ (fun W => W.det ^ ν * G W) =
      fun lam => clampedDeterminant δ ν lam * clampedSpectralAverage δ G lam :=
    funext (clamped_average_determinant_weight δ ν G)
  rw [he] at hi
  exact hi

theorem clamped_determinant_isotropic_integrable {n : ℕ} {α δ ν : ℝ}
    (hα : (n : ℝ) - 1 < α) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν) :
    Integrable (clampedDeterminant (n := n) δ ν) (isotropicEigenvalueLaw n α) := by
  have hi := clamped_weighted_average_isotropic_integrable hα hδ hδ1 hν
    (G := fun _ => (1 : ℝ)) continuousOn_const (C := 1) (β := 0) zero_le_one
    (fun _ _ => by simp)
  have he : clampedSpectralAverage (n := n) δ (fun _ => (1 : ℝ)) = fun _ => 1 := by
    funext lam
    simp only [clampedSpectralAverage, integral_const, probReal_univ, one_smul]
  simpa only [he, mul_one] using hi

end ResearchMain.WishartBlocks
