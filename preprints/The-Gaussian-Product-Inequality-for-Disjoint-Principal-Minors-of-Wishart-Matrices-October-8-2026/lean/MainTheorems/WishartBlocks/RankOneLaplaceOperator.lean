import MainTheorems.WishartBlocks.RankOnePrecisionAlgebra

namespace ResearchMain.WishartBlocks

open MeasureTheory Matrix
open scoped BigOperators InnerProductSpace

noncomputable def rankOneLaplaceOperatorValue {p : ℕ} (q : ℝ)
    (T W : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) : ℝ :=
  (-q * ⟪v, T.toEuclideanLin v⟫_ℝ +
      2 * (Matrix.vecMulVec (T *ᵥ fun i => v i) (T *ᵥ fun i => v i) * W).trace) *
    Real.exp (-(T * W).trace)

theorem rankOneLaplaceOperator_integrable {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    {S T : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hT : T.PosSemidef)
    (m v : EuclideanSpace ℝ (Fin p)) :
    Integrable (fun W => rankOneLaplaceOperatorValue q T W v) (oneRowWishartLaw q S m) := by
  have h₁ := (oneRowWishart_laplace_kernel_integrable hq S hT m).const_mul
    (-q * ⟪v, T.toEuclideanLin v⟫_ℝ)
  have h₂ := (oneRowWishart_laplace_weighted_trace_integrable hq hS hT m
    (Matrix.vecMulVec (T *ᵥ fun i => v i) (T *ᵥ fun i => v i))).const_mul 2
  apply (h₁.add h₂).congr
  exact ae_of_all _ fun W => by
    dsimp only [Pi.add_apply, rankOneLaplaceOperatorValue]
    ring

theorem rankOneLaplaceOperator_expectation {p : ℕ} {q θ : ℝ} (hq : (p : ℝ) < q)
    (hθ : 0 ≤ θ) {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosSemidef) (v : EuclideanSpace ℝ (Fin p)) :
    (∫ W, rankOneLaplaceOperatorValue q T W v
      ∂(oneRowWishartLaw q S (Real.sqrt θ • v))) =
      (-q * rankOneLaplaceRate S T v + 2 * θ * (rankOneLaplaceRate S T v) ^ 2) *
        rankOneLaplaceExpectation q S T v θ := by
  let P := 1 + (2 : ℝ) • (S * T)
  let H := Matrix.vecMulVec (T *ᵥ fun i => v i) (T *ᵥ fun i => v i)
  let h := (fun i => v i) ⬝ᵥ ((T * P⁻¹ * S * T) *ᵥ fun i => v i)
  let μ := oneRowWishartLaw q S (Real.sqrt θ • v)
  have hH : H.PosSemidef := by
    simpa only [H, star_trivial] using
      Matrix.posSemidef_vecMulVec_self_star (T *ᵥ fun i => v i)
  have hW := oneRowWishart_laplace_weighted_trace hq hS hT hH (Real.sqrt θ • v)
  rw [oneRowLaplaceDirectionalCoefficient_rankOne hθ hS hT v] at hW
  have hC : oneRowLaplaceClosed q S T (Real.sqrt θ • v) =
      rankOneLaplaceExpectation q S T v θ :=
    (oneRowLaplaceClosed_eq_expectation hq hS hT (Real.sqrt θ • v)).symm
  rw [hC] at hW
  have hD : IsUnit P.det :=
    isUnit_iff_ne_zero.mpr (covariance_precision_det_pos hS.posSemidef hT).ne'
  have hrel : rankOneLaplaceRate S T v + 2 * h = ⟪v, T.toEuclideanLin v⟫_ℝ := by
    have he := congrArg (fun A : Matrix (Fin p) (Fin p) ℝ =>
      (fun i => v i) ⬝ᵥ (A *ᵥ fun i => v i)) (covariance_resolvent_identity S T hD)
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
      euclidean_dotProduct_matrix v v (T * P⁻¹), euclidean_dotProduct_matrix v v T] at he
    exact he
  have h₁ := (oneRowWishart_laplace_kernel_integrable hq S hT (Real.sqrt θ • v)).const_mul
    (-q * ⟪v, T.toEuclideanLin v⟫_ℝ)
  have h₂ := (oneRowWishart_laplace_weighted_trace_integrable hq hS hT
    (Real.sqrt θ • v) H).const_mul 2
  have he : (fun W => rankOneLaplaceOperatorValue q T W v) =
      fun W => (-q * ⟪v, T.toEuclideanLin v⟫_ℝ) * Real.exp (-(T * W).trace) +
        2 * ((H * W).trace * Real.exp (-(T * W).trace)) := by
    funext W
    dsimp only [rankOneLaplaceOperatorValue, H]
    ring
  rw [he, integral_add h₁ h₂, integral_const_mul, integral_const_mul, hW]
  change (-q * ⟪v, T.toEuclideanLin v⟫_ℝ) * rankOneLaplaceExpectation q S T v θ +
    2 * (-rankOneLaplaceExpectation q S T v θ * (-q * h -
      θ * (rankOneLaplaceRate S T v) ^ 2)) = _
  rw [← hrel]
  ring

theorem rankOneLaplace_actual_operator_identity {p : ℕ} {q θ : ℝ}
    (hq : (p : ℝ) < q) (hθ : 0 < θ)
    {S T : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hT : T.PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) :
    2 * θ * deriv (deriv (rankOneLaplaceExpectation q S T v)) θ +
      q * deriv (rankOneLaplaceExpectation q S T v) θ =
      ∫ W, rankOneLaplaceOperatorValue q T W v
        ∂(oneRowWishartLaw q S (Real.sqrt θ • v)) := by
  rw [rankOneLaplaceExpectation_differential_identity hq hθ hS hT v,
    rankOneLaplaceOperator_expectation hq hθ.le hS hT v]

end ResearchMain.WishartBlocks
