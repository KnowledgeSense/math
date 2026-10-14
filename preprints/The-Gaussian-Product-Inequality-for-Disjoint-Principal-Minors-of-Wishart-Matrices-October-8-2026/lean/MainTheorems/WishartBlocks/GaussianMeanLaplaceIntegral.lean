import MainTheorems.WishartBlocks.GaussianMeanLaplace

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped BigOperators InnerProductSpace Topology Matrix.Norms.Elementwise

noncomputable def gaussianMeanLaplaceExpectation {p : ℕ} (q : ℝ)
    (S T : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : ℝ :=
  ∫ x, gaussianMeanLaplace S T v s x ∂(oneRowInputLaw q S)

theorem gaussianMeanLaplaceExpectation_hasDerivAt {p : ℕ} {q : ℝ}
    (hq : (p : ℝ) < q) (S : Matrix (Fin p) (Fin p) ℝ)
    {T : Matrix (Fin p) (Fin p) ℝ} (hT : T.PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    HasDerivAt (gaussianMeanLaplaceExpectation q S T v)
      (∫ x, gaussianMeanLaplaceFirst S T v s x ∂(oneRowInputLaw q S)) s := by
  let F := gaussianMeanLaplace S T v
  let F' := gaussianMeanLaplaceFirst S T v
  let C := 2 * ‖T.toEuclideanLin v‖ * oneRowGaussianBound S v s
  have hF (t : ℝ) : AEStronglyMeasurable (F t) (oneRowInputLaw q S) := by
    exact (gaussianMeanLaplace_measurable S T v t).aestronglyMeasurable
  have hF' : AEStronglyMeasurable (F' s) (oneRowInputLaw q S) := by
    exact (gaussianMeanLaplaceFirst_measurable S T v s).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(oneRowInputLaw q S), ∀ t ∈ Metric.ball s 1,
      ‖F' t x‖ ≤ C * (1 + ‖x‖) := by
    filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
    intro t ht
    exact gaussianMeanLaplaceFirst_local_bound S hT v s
      (by simpa only [Metric.mem_ball, Real.dist_eq] using ht) hx
  have hi : Integrable (fun x : OneRowInput p => C * (1 + ‖x‖)) (oneRowInputLaw q S) := by
    simpa only [pow_one] using (oneRowInput_polynomial_integrable hq S 1).const_mul C
  have hdiff : ∀ᵐ x ∂(oneRowInputLaw q S), ∀ t ∈ Metric.ball s 1,
      HasDerivAt (fun t => F t x) (F' t x) t :=
    ae_of_all _ fun x t _ => gaussianMeanLaplace_hasDerivAt S hT.1 v t x
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s zero_lt_one) (Filter.Eventually.of_forall hF)
    (gaussianMeanLaplace_integrable hq S hT v s) hF' hbound hi hdiff).2

theorem gaussianMeanLaplaceFirstIntegral_hasDerivAt {p : ℕ} {q : ℝ}
    (hq : (p : ℝ) < q) (S : Matrix (Fin p) (Fin p) ℝ)
    {T : Matrix (Fin p) (Fin p) ℝ} (hT : T.PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    HasDerivAt (fun t => ∫ x, gaussianMeanLaplaceFirst S T v t x ∂(oneRowInputLaw q S))
      (∫ x, gaussianMeanLaplaceSecond S T v s x ∂(oneRowInputLaw q S)) s := by
  let F := gaussianMeanLaplaceFirst S T v
  let F' := gaussianMeanLaplaceSecond S T v
  let C := 4 * (‖T.toEuclideanLin v‖ * oneRowGaussianBound S v s) ^ 2 +
    2 * |⟪v, T.toEuclideanLin v⟫_ℝ|
  have hF (t : ℝ) : AEStronglyMeasurable (F t) (oneRowInputLaw q S) := by
    exact (gaussianMeanLaplaceFirst_measurable S T v t).aestronglyMeasurable
  have hF' : AEStronglyMeasurable (F' s) (oneRowInputLaw q S) := by
    exact (gaussianMeanLaplaceSecond_measurable S T v s).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(oneRowInputLaw q S), ∀ t ∈ Metric.ball s 1,
      ‖F' t x‖ ≤ C * (1 + ‖x‖) ^ 2 := by
    filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
    intro t ht
    exact gaussianMeanLaplaceSecond_local_bound S hT v s
      (by simpa only [Metric.mem_ball, Real.dist_eq] using ht) hx
  have hi := (oneRowInput_polynomial_integrable hq S 2).const_mul C
  have hdiff : ∀ᵐ x ∂(oneRowInputLaw q S), ∀ t ∈ Metric.ball s 1,
      HasDerivAt (fun t => F t x) (F' t x) t :=
    ae_of_all _ fun x t _ => gaussianMeanLaplaceFirst_hasDerivAt S hT.1 v t x
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s zero_lt_one) (Filter.Eventually.of_forall hF)
    (gaussianMeanLaplaceFirst_integrable hq S hT v s) hF' hbound hi hdiff).2

theorem gaussianMeanLaplaceExpectation_eq {p : ℕ} {q : ℝ}
    (hq : (p : ℝ) < q) {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosSemidef) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    gaussianMeanLaplaceExpectation q S T v s =
      (1 + (2 : ℝ) • (S * T)).det ^ (-q / 2) *
        Real.exp (-s ^ 2 * rankOneLaplaceRate S T v) := by
  have h := oneRowWishart_laplace hq hS hT (s • v)
  unfold oneRowWishartLaw at h
  rw [integral_map (measurable_oneRowWishartValue S (s • v)).aemeasurable
    (continuous_exp_trace_mul T).measurable.aestronglyMeasurable] at h
  change (∫ x, Real.exp (-(T * oneRowWishartValue S (s • v) x).trace)
    ∂((bartlettLaw (q - 1) S).prod (stdGaussian (EuclideanSpace ℝ (Fin p))))) = _
  rw [h]
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right, rankOneLaplaceRate]
  congr 2
  ring

theorem gaussianMeanLaplaceFirst_integral {p : ℕ} {q : ℝ}
    (hq : (p : ℝ) < q) {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosSemidef) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    (∫ x, gaussianMeanLaplaceFirst S T v s x ∂(oneRowInputLaw q S)) =
      -2 * s * rankOneLaplaceRate S T v * gaussianMeanLaplaceExpectation q S T v s := by
  let a := rankOneLaplaceRate S T v
  let C := (1 + (2 : ℝ) • (S * T)).det ^ (-q / 2)
  have he : gaussianMeanLaplaceExpectation q S T v =
      fun t => C * Real.exp (-t ^ 2 * a) := by
    funext t
    exact gaussianMeanLaplaceExpectation_eq hq hS hT v t
  have h := (((hasDerivAt_id' s).pow 2 |>.mul_const (-a)).exp).const_mul C
  have hd : HasDerivAt (gaussianMeanLaplaceExpectation q S T v)
      (-2 * s * a * gaussianMeanLaplaceExpectation q S T v s) s := by
    rw [he]
    convert h using 1
    · funext t
      dsimp only [Pi.pow_apply]
      congr 2
      ring
    · dsimp only [Pi.pow_apply]
      simp only [mul_neg, neg_mul]
      ring
  exact (gaussianMeanLaplaceExpectation_hasDerivAt hq S hT v s).unique hd

theorem gaussianMeanLaplaceSecond_integral {p : ℕ} {q : ℝ}
    (hq : (p : ℝ) < q) {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosSemidef) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    (∫ x, gaussianMeanLaplaceSecond S T v s x ∂(oneRowInputLaw q S)) =
      (4 * s ^ 2 * (rankOneLaplaceRate S T v) ^ 2 - 2 * rankOneLaplaceRate S T v) *
        gaussianMeanLaplaceExpectation q S T v s := by
  let a := rankOneLaplaceRate S T v
  have he : (fun t => ∫ x, gaussianMeanLaplaceFirst S T v t x ∂(oneRowInputLaw q S)) =
      fun t => -2 * t * a * gaussianMeanLaplaceExpectation q S T v t := by
    funext t
    exact gaussianMeanLaplaceFirst_integral hq hS hT v t
  have hE := gaussianMeanLaplaceExpectation_hasDerivAt hq S hT v s
  rw [gaussianMeanLaplaceFirst_integral hq hS hT v s] at hE
  have h := (((hasDerivAt_id' s).const_mul (-2)).mul_const a).mul hE
  have hd : HasDerivAt
      (fun t => ∫ x, gaussianMeanLaplaceFirst S T v t x ∂(oneRowInputLaw q S))
      ((4 * s ^ 2 * a ^ 2 - 2 * a) * gaussianMeanLaplaceExpectation q S T v s) s := by
    rw [he]
    convert h using 1
    dsimp only [a]
    ring
  exact (gaussianMeanLaplaceFirstIntegral_hasDerivAt hq S hT v s).unique hd

theorem gaussianMeanLaplace_integral_operator_identity {p : ℕ} {q s : ℝ}
    (hq : (p : ℝ) < q) (hs : 0 < s) {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosSemidef) (v : EuclideanSpace ℝ (Fin p)) :
    (∫ x, gaussianMeanLaplaceSecond S T v s x ∂(oneRowInputLaw q S)) / 2 +
      (q - 1) * (∫ x, gaussianMeanLaplaceFirst S T v s x ∂(oneRowInputLaw q S)) / (2 * s) =
      ∫ W, rankOneLaplaceOperatorValue q T W v ∂(oneRowWishartLaw q S (s • v)) := by
  have he : gaussianMeanLaplaceExpectation q S T v s =
      rankOneLaplaceExpectation q S T v (s ^ 2) := by
    unfold gaussianMeanLaplaceExpectation gaussianMeanLaplace laplaceMatrixTest
      rankOneLaplaceExpectation oneRowWishartLaw
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hs,
      integral_map (measurable_oneRowWishartValue S (s • v)).aemeasurable
        (continuous_exp_trace_mul T).measurable.aestronglyMeasurable]
    rfl
  have h := rankOneLaplaceOperator_expectation hq (sq_nonneg s) hS hT v
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hs, ← he] at h
  rw [gaussianMeanLaplaceFirst_integral hq hS hT v s,
    gaussianMeanLaplaceSecond_integral hq hS hT v s, h]
  field_simp [hs.ne']
  ring

end ResearchMain.WishartBlocks
