import MainTheorems.WishartBlocks.PositiveLaplaceMoment
import MainTheorems.WishartBlocks.CovarianceLaplaceDerivatives
import MainTheorems.WishartBlocks.ShiftedDeterminantMoments

namespace ResearchMain.WishartBlocks

open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.Elementwise

theorem matrix_trace_mul_norm_bound {p : ℕ} (H W : Matrix (Fin p) (Fin p) ℝ) :
    ‖(H * W).trace‖ ≤ (p : ℝ) ^ 2 * ‖H‖ * ‖W‖ := by
  calc
    ‖(H * W).trace‖ = ‖∑ i, ∑ j, H i j * W j i‖ := rfl
    _ ≤ ∑ i, ∑ j, ‖H i j * W j i‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_le _ _
    _ ≤ ∑ _ : Fin p, ∑ _ : Fin p, ‖H‖ * ‖W‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul
        ((norm_le_pi_norm (H i) j).trans (norm_le_pi_norm H i))
        ((norm_le_pi_norm (W j) i).trans (norm_le_pi_norm W j))
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring

theorem oneRowWishart_trace_integrable {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (m : EuclideanSpace ℝ (Fin p)) (H : Matrix (Fin p) (Fin p) ℝ) :
    Integrable (fun W => (H * W).trace) (oneRowWishartLaw q S m) := by
  have hi := (oneRowWishart_polynomial_integrable hq hS m 1).const_mul
    ((p : ℝ) ^ 2 * ‖H‖)
  have hm : Measurable (fun W : Matrix (Fin p) (Fin p) ℝ => (H * W).trace) := by
    unfold Matrix.trace
    fun_prop
  apply hi.mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun W => by
    apply (matrix_trace_mul_norm_bound H W).trans
    simp only [pow_one]
    exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg W]) (by positivity)

theorem oneRowWishart_laplace_kernel_integrable {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) {T : Matrix (Fin p) (Fin p) ℝ}
    (hT : T.PosSemidef) (m : EuclideanSpace ℝ (Fin p)) :
    Integrable (fun W => Real.exp (-(T * W).trace)) (oneRowWishartLaw q S m) := by
  let : IsProbabilityMeasure (oneRowWishartLaw q S m) := oneRowWishart_probability hq S m
  apply (integrable_const (1 : ℝ)).mono'
    (continuous_exp_trace_mul T).measurable.aestronglyMeasurable
  filter_upwards [oneRowWishart_positiveSemidefinite q S m] with W hW
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (trace_positive_product hT hW))

theorem oneRowWishart_laplace_weighted_trace_integrable {p : ℕ} {q : ℝ}
    (hq : (p : ℝ) < q) {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosSemidef) (m : EuclideanSpace ℝ (Fin p))
    (H : Matrix (Fin p) (Fin p) ℝ) :
    Integrable (fun W => (H * W).trace * Real.exp (-(T * W).trace))
      (oneRowWishartLaw q S m) := by
  have hm : Measurable (fun W : Matrix (Fin p) (Fin p) ℝ => (H * W).trace) := by
    unfold Matrix.trace
    fun_prop
  apply (oneRowWishart_trace_integrable hq hS m H).norm.mono'
    (hm.fun_mul (continuous_exp_trace_mul T).measurable).aestronglyMeasurable
  filter_upwards [oneRowWishart_positiveSemidefinite q S m] with W hW
  have he : Real.exp (-(T * W).trace) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (trace_positive_product hT hW))
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (norm_nonneg _)

theorem oneRowWishart_laplace_weighted_trace {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    {S T H : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hT : T.PosSemidef) (hH : H.PosSemidef) (m : EuclideanSpace ℝ (Fin p)) :
    (∫ W, (H * W).trace * Real.exp (-(T * W).trace) ∂(oneRowWishartLaw q S m)) =
      -oneRowLaplaceClosed q S T m * oneRowLaplaceDirectionalCoefficient q S T H m := by
  let μ := oneRowWishartLaw q S m
  let : IsProbabilityMeasure μ := oneRowWishart_probability hq S m
  have ha0 : ∀ᵐ W ∂μ, 0 ≤ (T * W).trace := by
    filter_upwards [oneRowWishart_positiveSemidefinite q S m] with W hW
    exact trace_positive_product hT hW
  have hb0 : ∀ᵐ W ∂μ, 0 ≤ (H * W).trace := by
    filter_upwards [oneRowWishart_positiveSemidefinite q S m] with W hW
    exact trace_positive_product hH hW
  have hMoment := positive_laplace_moment_hasDerivWithinAt_zero μ
    (by unfold Matrix.trace; fun_prop : Measurable (fun W => (T * W).trace))
    (by unfold Matrix.trace; fun_prop : Measurable (fun W => (H * W).trace)) ha0 hb0
    (oneRowWishart_trace_integrable hq hS m H)
  have hClosed := oneRowLaplaceClosed_directional q S T H m
    (covariance_precision_det_pos hS.posSemidef hT)
  have he : (fun t : ℝ => ∫ W, Real.exp (-(T * W).trace - t * (H * W).trace) ∂μ) =ᶠ[
      nhdsWithin 0 (Set.Ici 0)] fun t => oneRowLaplaceClosed q S (T + t • H) m := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 ≤ t := Set.mem_Ici.mp ht
    rw [← oneRowLaplaceClosed_eq_expectation hq hS (hT.add (hH.smul ht')) m]
    apply integral_congr_ae
    exact ae_of_all _ fun W => by
      simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
        smul_eq_mul]
      congr 1
      ring
  have hClosed' := hClosed.hasDerivWithinAt.congr_of_eventuallyEq_of_mem he
    (show (0 : ℝ) ∈ Set.Ici 0 by simp)
  have hEq := UniqueDiffWithinAt.eq_deriv (Set.Ici (0 : ℝ))
    (uniqueDiffWithinAt_Ici (0 : ℝ)) hMoment hClosed'
  simp only [integral_neg, neg_mul] at hEq
  dsimp only [μ] at hEq
  linarith

end ResearchMain.WishartBlocks
