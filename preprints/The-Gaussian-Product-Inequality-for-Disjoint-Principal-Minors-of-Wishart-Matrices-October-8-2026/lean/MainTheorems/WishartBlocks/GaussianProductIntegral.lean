import MainTheorems.WishartBlocks.GaussianProductGrowth
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace ResearchMain.WishartBlocks

open MeasureTheory Filter Matrix
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Elementwise

theorem oneRowInput_real_power_integrable {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (β : ℝ) :
    Integrable (fun x : OneRowInput p => (1 + ‖x‖) ^ β) (oneRowInputLaw q S) := by
  apply oneRowInput_real_growth_integrable hq S (by fun_prop) zero_le_one
  intro x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) β), one_mul]

namespace BlockPartition

noncomputable def gaussianProductExpectation {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε q : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : ℂ :=
  ∫ x, gaussianMatrixTest (P.smoothProductEuclidean ν ε) S v s x ∂(oneRowInputLaw q S)

noncomputable def gaussianProductFirstIntegral {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε q : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : ℂ :=
  ∫ x, gaussianMatrixTestFirst (P.smoothProductEuclidean ν ε) S v s x ∂(oneRowInputLaw q S)

noncomputable def gaussianProductSecondIntegral {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε q : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : ℂ :=
  ∫ x, gaussianMatrixTestSecond (P.smoothProductEuclidean ν ε) S v s x ∂(oneRowInputLaw q S)

theorem gaussianProduct_integrable {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε q : ℝ} (hε : 0 < ε) (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Integrable (gaussianMatrixTest (P.smoothProductEuclidean ν ε) S v s) (oneRowInputLaw q S) := by
  have hi := P.regularizedProduct_latent_weight_integrable hq S v s ε ν hν 0
  simp only [pow_zero, one_mul] at hi
  apply hi.mono' (gaussianMatrixTest_measurable (P.smoothProductEuclidean_contDiff ν hε)
    S v s).aestronglyMeasurable
  filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
  have h := P.smoothProductEuclidean_jet_zero ν hε (oneRowWishartValue_positive S v s hx)
  simpa only [gaussianMatrixTest, norm_iteratedFDeriv_zero,
    Real.norm_of_nonneg (norm_nonneg _)] using h.le

theorem gaussianProductFirst_integrable {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε q : ℝ} (hε : 0 < ε) (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Integrable (gaussianMatrixTestFirst (P.smoothProductEuclidean ν ε) S v s)
      (oneRowInputLaw q S) := by
  let C := P.localProductConstant ν ε S v s * P.regularizedJetConstant ν ε 1 *
    localFirstMatrixConstant S v s
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (P.localProductConstant_nonneg ν ε S v s) (P.regularizedJetConstant_nonneg ν hε 1))
      (localFirstMatrixConstant_nonneg S v s)
  apply ((oneRowInput_real_power_integrable hq S (2 * P.productGrowthExponent ν + 1)).const_mul C).mono'
    ((gaussianMatrixTestFirst_measurable (P.smoothProductEuclidean_contDiff ν hε) S v s).aestronglyMeasurable)
  filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
  exact P.gaussianProductFirst_local_bound ν hν hε S v s (by simp) hx

theorem gaussianProductSecond_integrable {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε q : ℝ} (hε : 0 < ε) (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Integrable (gaussianMatrixTestSecond (P.smoothProductEuclidean ν ε) S v s)
      (oneRowInputLaw q S) := by
  let C := P.localProductConstant ν ε S v s *
    (P.regularizedJetConstant ν ε 2 * localFirstMatrixConstant S v s ^ 2 +
      P.regularizedJetConstant ν ε 1 * secondMatrixConstant v)
  have hC : 0 ≤ C := by
    have hA := P.localProductConstant_nonneg ν ε S v s
    have hK₁ := P.regularizedJetConstant_nonneg ν hε 1
    have hK₂ := P.regularizedJetConstant_nonneg ν hε 2
    have hE := secondMatrixConstant_nonneg v
    dsimp only [C]
    positivity
  apply ((oneRowInput_real_power_integrable hq S (2 * P.productGrowthExponent ν + 2)).const_mul C).mono'
    ((gaussianMatrixTestSecond_measurable (P.smoothProductEuclidean_contDiff ν hε) S v s).aestronglyMeasurable)
  filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
  exact P.gaussianProductSecond_local_bound ν hν hε S v s (by simp) hx

theorem gaussianProductExpectation_hasDerivAt {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε q : ℝ} (hε : 0 < ε) (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    HasDerivAt (P.gaussianProductExpectation ν ε q S v)
      (P.gaussianProductFirstIntegral ν ε q S v s) s := by
  let f := P.smoothProductEuclidean ν ε
  let C := P.localProductConstant ν ε S v s * P.regularizedJetConstant ν ε 1 *
    localFirstMatrixConstant S v s
  have hf := P.smoothProductEuclidean_contDiff ν hε
  have hbound : ∀ᵐ x ∂(oneRowInputLaw q S), ∀ t ∈ Metric.ball s 1,
      ‖gaussianMatrixTestFirst f S v t x‖ ≤ C * (1 + ‖x‖) ^ (2 * P.productGrowthExponent ν + 1) := by
    filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
    intro t ht
    exact P.gaussianProductFirst_local_bound ν hν hε S v s
      (by simpa only [Metric.mem_ball, Real.dist_eq] using ht) hx
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s zero_lt_one)
    (Eventually.of_forall fun t => (gaussianMatrixTest_measurable hf S v t).aestronglyMeasurable)
    (P.gaussianProduct_integrable ν hν hε hq S v s)
    (gaussianMatrixTestFirst_measurable hf S v s).aestronglyMeasurable hbound
    ((oneRowInput_real_power_integrable hq S (2 * P.productGrowthExponent ν + 1)).const_mul C)
    (ae_of_all _ fun x t _ => gaussianMatrixTest_hasDerivAt hf S v t x)).2

theorem gaussianProductFirstIntegral_hasDerivAt {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε q : ℝ} (hε : 0 < ε) (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    HasDerivAt (P.gaussianProductFirstIntegral ν ε q S v)
      (P.gaussianProductSecondIntegral ν ε q S v s) s := by
  let f := P.smoothProductEuclidean ν ε
  let C := P.localProductConstant ν ε S v s *
    (P.regularizedJetConstant ν ε 2 * localFirstMatrixConstant S v s ^ 2 +
      P.regularizedJetConstant ν ε 1 * secondMatrixConstant v)
  have hf := P.smoothProductEuclidean_contDiff ν hε
  have hbound : ∀ᵐ x ∂(oneRowInputLaw q S), ∀ t ∈ Metric.ball s 1,
      ‖gaussianMatrixTestSecond f S v t x‖ ≤ C * (1 + ‖x‖) ^ (2 * P.productGrowthExponent ν + 2) := by
    filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
    intro t ht
    exact P.gaussianProductSecond_local_bound ν hν hε S v s
      (by simpa only [Metric.mem_ball, Real.dist_eq] using ht) hx
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s zero_lt_one)
    (Eventually.of_forall fun t => (gaussianMatrixTestFirst_measurable hf S v t).aestronglyMeasurable)
    (P.gaussianProductFirst_integrable ν hν hε hq S v s)
    (gaussianMatrixTestSecond_measurable hf S v s).aestronglyMeasurable hbound
    ((oneRowInput_real_power_integrable hq S (2 * P.productGrowthExponent ν + 2)).const_mul C)
    (ae_of_all _ fun x t _ => gaussianMatrixTestFirst_hasDerivAt hf S v t x)).2

theorem gaussianProductExpectation_actualLaw {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε q : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) {hε : 0 < ε} :
    P.gaussianProductExpectation ν ε q S v s =
      ∫ W, (P.smoothRegularizedProduct ν ε W : ℂ) ∂(oneRowWishartLaw q S (s • v)) := by
  have hm : Measurable (fun W : Matrix (Fin p) (Fin p) ℝ =>
      (P.smoothRegularizedProduct ν ε W : ℂ)) :=
    Continuous.measurable (α := Fin p → Fin p → ℝ)
      (Complex.ofRealCLM.contDiff.comp (P.smoothRegularizedProduct_contDiff ν hε)).continuous
  unfold oneRowWishartLaw
  rw [integral_map (measurable_oneRowWishartValue S (s • v)).aemeasurable
    hm.aestronglyMeasurable]
  rfl

theorem gaussianProductExpectation_even {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε q : ℝ} (hε : 0 < ε) (hq : (p : ℝ) < q)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    P.gaussianProductExpectation ν ε q S v (-s) = P.gaussianProductExpectation ν ε q S v s := by
  rw [P.gaussianProductExpectation_actualLaw (hε := hε),
    P.gaussianProductExpectation_actualLaw (hε := hε), neg_smul,
    oneRowWishart_neg_mean hq hS]

end BlockPartition
end ResearchMain.WishartBlocks
