import MainTheorems.WishartBlocks.GaussianMeanLaplaceIntegral

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.Elementwise

theorem trace_two_vectorGrams {p : ℕ} (u y : EuclideanSpace ℝ (Fin p)) :
    (Matrix.vecMulVec (fun i => u i) (fun i => u i) *
      Matrix.vecMulVec (fun i => y i) (fun i => y i)).trace = ⟪y, u⟫_ℝ ^ 2 := by
  rw [trace_matrix_outer, Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul]
  have hi : (fun i => u i) ⬝ᵥ (fun i => y i) = ⟪y, u⟫_ℝ := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply,
      star_trivial, dotProduct]
  have hi' : (fun i => y i) ⬝ᵥ (fun i => u i) = ⟪y, u⟫_ℝ := by
    rw [dotProduct_comm, hi]
  rw [hi, hi']
  ring

noncomputable def rankOneDifferenceLaplace {p : ℕ} (q : ℝ)
    (S T : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p))
    (s : ℝ) (x : OneRowInput p) : ℝ :=
  ((q - 1) * (⟪v, T.toEuclideanLin v⟫_ℝ -
      ⟪oneRowGaussianVector S v s x, T.toEuclideanLin v⟫_ℝ / s) -
    2 * (Matrix.vecMulVec (T *ᵥ fun i => v i) (T *ᵥ fun i => v i) * x.1).trace) *
      gaussianMeanLaplace S T v s x

theorem gaussianMeanLaplace_operator_difference {p : ℕ} (q : ℝ)
    (S T : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p))
    (s : ℝ) (hs : s ≠ 0) (x : OneRowInput p) :
    gaussianMeanLaplaceSecond S T v s x / 2 +
      (q - 1) * gaussianMeanLaplaceFirst S T v s x / (2 * s) -
      rankOneLaplaceOperatorValue q T (oneRowWishartValue S (s • v) x) v =
      rankOneDifferenceLaplace q S T v s x := by
  have ht : (Matrix.vecMulVec (T *ᵥ fun i => v i) (T *ᵥ fun i => v i) *
      gaussianMeanGram S (s • v) x.2).trace =
      ⟪oneRowGaussianVector S v s x, T.toEuclideanLin v⟫_ℝ ^ 2 := by
    exact trace_two_vectorGrams (T.toEuclideanLin v) (oneRowGaussianVector S v s x)
  have he : Real.exp (-((T * x.1).trace +
      (T * gaussianMeanGram S (s • v) x.2).trace)) =
      gaussianMeanLaplace S T v s x := by
    simp only [gaussianMeanLaplace, laplaceMatrixTest, oneRowWishartValue,
      Matrix.mul_add, Matrix.trace_add]
  simp only [gaussianMeanLaplaceSecond, gaussianMeanLaplaceFirst,
    rankOneLaplaceOperatorValue, oneRowWishartValue, Matrix.mul_add, Matrix.trace_add,
    ht, rankOneDifferenceLaplace, he]
  field_simp [hs]
  ring

theorem rankOneDifferenceLaplace_integrable {p : ℕ} {q s : ℝ}
    (hq : (p : ℝ) < q) (hs : 0 < s) {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosSemidef) (v : EuclideanSpace ℝ (Fin p)) :
    Integrable (rankOneDifferenceLaplace q S T v s) (oneRowInputLaw q S) := by
  have hR : Integrable (fun x =>
      rankOneLaplaceOperatorValue q T (oneRowWishartValue S (s • v) x) v)
      (oneRowInputLaw q S) := by
    exact (integrable_map_measure (by
        dsimp [rankOneLaplaceOperatorValue]
        fun_prop) (measurable_oneRowWishartValue S (s • v)).aemeasurable).mp
      (rankOneLaplaceOperator_integrable hq hS hT (s • v) v)
  have h := ((gaussianMeanLaplaceSecond_integrable hq S hT v s).div_const 2).add
    (((gaussianMeanLaplaceFirst_integrable hq S hT v s).const_mul (q - 1)).div_const (2 * s))
  apply (h.sub hR).congr
  exact ae_of_all _ fun x => gaussianMeanLaplace_operator_difference q S T v s hs.ne' x

theorem rankOneDifferenceLaplace_integral_zero {p : ℕ} {q s : ℝ}
    (hq : (p : ℝ) < q) (hs : 0 < s) {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosSemidef) (v : EuclideanSpace ℝ (Fin p)) :
    (∫ x, rankOneDifferenceLaplace q S T v s x ∂(oneRowInputLaw q S)) = 0 := by
  have hR : Integrable (fun x =>
      rankOneLaplaceOperatorValue q T (oneRowWishartValue S (s • v) x) v)
      (oneRowInputLaw q S) := by
    exact (integrable_map_measure (by
        dsimp [rankOneLaplaceOperatorValue]
        fun_prop) (measurable_oneRowWishartValue S (s • v)).aemeasurable).mp
      (rankOneLaplaceOperator_integrable hq hS hT (s • v) v)
  have h₂ := (gaussianMeanLaplaceSecond_integrable hq S hT v s).div_const 2
  have h₁ := ((gaussianMeanLaplaceFirst_integrable hq S hT v s).const_mul (q - 1)).div_const (2 * s)
  have he : rankOneDifferenceLaplace q S T v s = fun x =>
      gaussianMeanLaplaceSecond S T v s x / 2 +
        (q - 1) * gaussianMeanLaplaceFirst S T v s x / (2 * s) -
        rankOneLaplaceOperatorValue q T (oneRowWishartValue S (s • v) x) v := by
    funext x
    exact (gaussianMeanLaplace_operator_difference q S T v s hs.ne' x).symm
  rw [he]
  change (∫ x, (((fun x => gaussianMeanLaplaceSecond S T v s x / 2) +
    (fun x => (q - 1) * gaussianMeanLaplaceFirst S T v s x / (2 * s))) -
    (fun x => rankOneLaplaceOperatorValue q T (oneRowWishartValue S (s • v) x) v)) x
    ∂(oneRowInputLaw q S)) = 0
  simp only [Pi.sub_apply]
  rw [integral_sub (h₂.add h₁) hR]
  simp only [Pi.add_apply]
  rw [integral_add h₂ h₁, integral_div, integral_div, integral_const_mul]
  have hmap : (∫ x, rankOneLaplaceOperatorValue q T
      (oneRowWishartValue S (s • v) x) v ∂(oneRowInputLaw q S)) =
      ∫ W, rankOneLaplaceOperatorValue q T W v ∂(oneRowWishartLaw q S (s • v)) := by
    unfold oneRowWishartLaw
    rw [integral_map (measurable_oneRowWishartValue S (s • v)).aemeasurable (by
      dsimp [rankOneLaplaceOperatorValue]
      fun_prop)]
    rfl
  rw [hmap, gaussianMeanLaplace_integral_operator_identity hq hs hS hT v]
  ring

end ResearchMain.WishartBlocks
