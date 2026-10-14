import MainTheorems.WishartBlocks.RegularizationLimit

namespace ResearchMain.WishartBlocks

open MeasureTheory Matrix Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise ContDiff

structure PolynomialPSDTest (p : ℕ) where
  toFun : MatrixEuclidean p → ℂ
  smooth : ContDiff ℝ ∞ toFun
  exponent : ℝ
  exponent_nonneg : 0 ≤ exponent
  jetConstant : ℕ → ℝ
  jetConstant_nonneg : ∀ k, 0 ≤ jetConstant k
  jet_bound : ∀ k ≤ 2, ∀ W : Matrix (Fin p) (Fin p) ℝ, W.PosSemidef →
    ‖iteratedFDeriv ℝ k toFun (matrixCoordinates p W)‖ ≤
      jetConstant k * (1 + ‖W‖) ^ exponent

namespace PolynomialPSDTest

open BlockPartition

noncomputable def localConstant {p : ℕ} (F : PolynomialPSDTest p)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (k : ℕ) : ℝ :=
  F.jetConstant k * (1 + oneRowMatrixBound S v (|s| + 1)) ^ F.exponent

theorem localConstant_nonneg {p : ℕ} (F : PolynomialPSDTest p)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (k : ℕ) :
    0 ≤ F.localConstant S v s k := by
  exact mul_nonneg (F.jetConstant_nonneg k) (Real.rpow_nonneg (by dsimp [oneRowMatrixBound]; positivity) _)

theorem local_jet_bound {p : ℕ} (F : PolynomialPSDTest p)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ)
    {t : ℝ} (ht : |t - s| < 1) {x : OneRowInput p} (hx : x.1.PosSemidef)
    {k : ℕ} (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k F.toFun (matrixCoordinates p (oneRowWishartValue S (t • v) x))‖ ≤
      F.localConstant S v s k * (1 + ‖x‖) ^ (2 * F.exponent) := by
  have hW := oneRowWishartValue_positive S v t hx
  have hB : 1 + ‖oneRowWishartValue S (t • v) x‖ ≤
      (1 + oneRowMatrixBound S v (|s| + 1)) * (1 + ‖x‖) ^ 2 := by
    have h := oneRowWishartValue_local_norm_bound S v s ht x
    nlinarith [norm_nonneg x]
  calc
    _ ≤ F.jetConstant k * (1 + ‖oneRowWishartValue S (t • v) x‖) ^ F.exponent := F.jet_bound k hk _ hW
    _ ≤ F.jetConstant k *
        ((1 + oneRowMatrixBound S v (|s| + 1)) * (1 + ‖x‖) ^ 2) ^ F.exponent :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hB F.exponent_nonneg)
        (F.jetConstant_nonneg k)
    _ = _ := by
      rw [Real.mul_rpow (by dsimp [oneRowMatrixBound]; positivity) (by positivity),
        ← Real.rpow_natCast_mul (by positivity) 2]
      dsimp only [localConstant]
      norm_num only [Nat.cast_ofNat]
      ring

theorem local_value_bound {p : ℕ} (F : PolynomialPSDTest p)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ)
    {t : ℝ} (ht : |t - s| < 1) {x : OneRowInput p} (hx : x.1.PosSemidef) :
    ‖gaussianMatrixTest F.toFun S v t x‖ ≤
      F.localConstant S v s 0 * (1 + ‖x‖) ^ (2 * F.exponent) := by
  simpa only [norm_iteratedFDeriv_zero, gaussianMatrixTest] using F.local_jet_bound S v s ht hx (k := 0) (by norm_num)

theorem local_first_bound {p : ℕ} (F : PolynomialPSDTest p)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ)
    {t : ℝ} (ht : |t - s| < 1) {x : OneRowInput p} (hx : x.1.PosSemidef) :
    ‖gaussianMatrixTestFirst F.toFun S v t x‖ ≤
      (F.localConstant S v s 1 * localFirstMatrixConstant S v s) *
        (1 + ‖x‖) ^ (2 * F.exponent + 1) := by
  have hA := F.localConstant_nonneg S v s 1
  have hD := localFirstMatrixConstant_nonneg S v s
  apply (gaussianMatrixTestFirst_jet_bound _ S v t x).trans
  calc
    _ ≤ (F.localConstant S v s 1 * (1 + ‖x‖) ^ (2 * F.exponent)) *
        (localFirstMatrixConstant S v s * (1 + ‖x‖)) :=
      mul_le_mul (F.local_jet_bound S v s ht hx (by norm_num : 1 ≤ 2))
        (first_matrix_local_bound S v s ht x) (norm_nonneg _) (by positivity)
    _ = _ := by rw [Real.rpow_add (by positivity), Real.rpow_one]; ring

theorem local_second_bound {p : ℕ} (F : PolynomialPSDTest p)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ)
    {t : ℝ} (ht : |t - s| < 1) {x : OneRowInput p} (hx : x.1.PosSemidef) :
    ‖gaussianMatrixTestSecond F.toFun S v t x‖ ≤
      (F.localConstant S v s 2 * localFirstMatrixConstant S v s ^ 2 +
        F.localConstant S v s 1 * secondMatrixConstant v) *
          (1 + ‖x‖) ^ (2 * F.exponent + 2) := by
  have h2 : 1 ≤ (1 + ‖x‖) ^ (2 : ℕ) := by nlinarith [norm_nonneg x]
  have hA1 := F.localConstant_nonneg S v s 1
  have hA2 := F.localConstant_nonneg S v s 2
  have hD := localFirstMatrixConstant_nonneg S v s
  have hE := secondMatrixConstant_nonneg v
  apply (gaussianMatrixTestSecond_jet_bound _ S v t x).trans
  calc
    _ ≤ (F.localConstant S v s 2 * (1 + ‖x‖) ^ (2 * F.exponent)) *
        (localFirstMatrixConstant S v s * (1 + ‖x‖)) ^ 2 +
      (F.localConstant S v s 1 * (1 + ‖x‖) ^ (2 * F.exponent)) * secondMatrixConstant v := by
      apply add_le_add
      · exact mul_le_mul (F.local_jet_bound S v s ht hx (by norm_num : 2 ≤ 2))
          (pow_le_pow_left₀ (norm_nonneg _) (first_matrix_local_bound S v s ht x) 2)
          (sq_nonneg _) (by positivity)
      · exact mul_le_mul (F.local_jet_bound S v s ht hx (by norm_num : 1 ≤ 2))
          (second_matrix_bound v) (norm_nonneg _) (by positivity)
    _ ≤ (F.localConstant S v s 2 * (1 + ‖x‖) ^ (2 * F.exponent)) *
        (localFirstMatrixConstant S v s * (1 + ‖x‖)) ^ 2 +
      (F.localConstant S v s 1 * (1 + ‖x‖) ^ (2 * F.exponent)) *
        secondMatrixConstant v * (1 + ‖x‖) ^ (2 : ℕ) := by
      apply add_le_add le_rfl
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h2
        (by positivity : 0 ≤
          (F.localConstant S v s 1 * (1 + ‖x‖) ^ (2 * F.exponent)) * secondMatrixConstant v)
    _ = _ := by rw [Real.rpow_add (by positivity), Real.rpow_two]; ring

theorem value_integrable {p : ℕ} (F : PolynomialPSDTest p) {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Integrable (gaussianMatrixTest F.toFun S v s) (oneRowInputLaw q S) := by
  apply ((oneRowInput_real_power_integrable hq S (2 * F.exponent)).const_mul
    (F.localConstant S v s 0)).mono' (gaussianMatrixTest_measurable F.smooth S v s).aestronglyMeasurable
  filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
  exact F.local_value_bound S v s (by simp) hx

theorem first_integrable {p : ℕ} (F : PolynomialPSDTest p) {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Integrable (gaussianMatrixTestFirst F.toFun S v s) (oneRowInputLaw q S) := by
  apply ((oneRowInput_real_power_integrable hq S (2 * F.exponent + 1)).const_mul
    (F.localConstant S v s 1 * localFirstMatrixConstant S v s)).mono'
      (gaussianMatrixTestFirst_measurable F.smooth S v s).aestronglyMeasurable
  filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
  exact F.local_first_bound S v s (by simp) hx

theorem second_integrable {p : ℕ} (F : PolynomialPSDTest p) {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Integrable (gaussianMatrixTestSecond F.toFun S v s) (oneRowInputLaw q S) := by
  apply ((oneRowInput_real_power_integrable hq S (2 * F.exponent + 2)).const_mul
    (F.localConstant S v s 2 * localFirstMatrixConstant S v s ^ 2 +
      F.localConstant S v s 1 * secondMatrixConstant v)).mono'
      (gaussianMatrixTestSecond_measurable F.smooth S v s).aestronglyMeasurable
  filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
  exact F.local_second_bound S v s (by simp) hx

noncomputable def expectation {p : ℕ} (F : PolynomialPSDTest p) (q : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : ℂ :=
  ∫ x, gaussianMatrixTest F.toFun S v s x ∂(oneRowInputLaw q S)

noncomputable def firstIntegral {p : ℕ} (F : PolynomialPSDTest p) (q : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : ℂ :=
  ∫ x, gaussianMatrixTestFirst F.toFun S v s x ∂(oneRowInputLaw q S)

noncomputable def secondIntegral {p : ℕ} (F : PolynomialPSDTest p) (q : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : ℂ :=
  ∫ x, gaussianMatrixTestSecond F.toFun S v s x ∂(oneRowInputLaw q S)

theorem expectation_hasDerivAt {p : ℕ} (F : PolynomialPSDTest p) {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    HasDerivAt (F.expectation q S v) (F.firstIntegral q S v s) s := by
  have hbound : ∀ᵐ x ∂(oneRowInputLaw q S), ∀ t ∈ Metric.ball s 1,
      ‖gaussianMatrixTestFirst F.toFun S v t x‖ ≤
        (F.localConstant S v s 1 * localFirstMatrixConstant S v s) * (1 + ‖x‖) ^ (2 * F.exponent + 1) := by
    filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
    intro t ht
    exact F.local_first_bound S v s (by simpa only [Metric.mem_ball, Real.dist_eq] using ht) hx
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s zero_lt_one)
    (Eventually.of_forall fun t => (gaussianMatrixTest_measurable F.smooth S v t).aestronglyMeasurable)
    (F.value_integrable hq S v s) (gaussianMatrixTestFirst_measurable F.smooth S v s).aestronglyMeasurable
    hbound ((oneRowInput_real_power_integrable hq S (2 * F.exponent + 1)).const_mul
      (F.localConstant S v s 1 * localFirstMatrixConstant S v s))
    (ae_of_all _ fun x t _ => gaussianMatrixTest_hasDerivAt F.smooth S v t x)).2

theorem firstIntegral_hasDerivAt {p : ℕ} (F : PolynomialPSDTest p) {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    HasDerivAt (F.firstIntegral q S v) (F.secondIntegral q S v s) s := by
  have hbound : ∀ᵐ x ∂(oneRowInputLaw q S), ∀ t ∈ Metric.ball s 1,
      ‖gaussianMatrixTestSecond F.toFun S v t x‖ ≤
        (F.localConstant S v s 2 * localFirstMatrixConstant S v s ^ 2 +
          F.localConstant S v s 1 * secondMatrixConstant v) * (1 + ‖x‖) ^ (2 * F.exponent + 2) := by
    filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
    intro t ht
    exact F.local_second_bound S v s (by simpa only [Metric.mem_ball, Real.dist_eq] using ht) hx
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s zero_lt_one)
    (Eventually.of_forall fun t => (gaussianMatrixTestFirst_measurable F.smooth S v t).aestronglyMeasurable)
    (F.first_integrable hq S v s) (gaussianMatrixTestSecond_measurable F.smooth S v s).aestronglyMeasurable
    hbound ((oneRowInput_real_power_integrable hq S (2 * F.exponent + 2)).const_mul
      (F.localConstant S v s 2 * localFirstMatrixConstant S v s ^ 2 +
        F.localConstant S v s 1 * secondMatrixConstant v))
    (ae_of_all _ fun x t _ => gaussianMatrixTestFirst_hasDerivAt F.smooth S v t x)).2

end PolynomialPSDTest
end ResearchMain.WishartBlocks
