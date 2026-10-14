import MainTheorems.WishartBlocks.NoncentralProductResponse
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable

namespace ResearchMain.WishartBlocks

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology MatrixOrder Matrix.Norms.Elementwise

abbrev NoncentralInput (p r : ℕ) :=
  Matrix (Fin p) (Fin p) ℝ × (Fin r → EuclideanSpace ℝ (Fin p))

noncomputable def noncentralInputLaw {p r : ℕ} (α : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measure (NoncentralInput p r) :=
  (bartlettLaw (α - (r : ℝ)) S).prod
    (Measure.pi fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin p)))

theorem noncentralInput_probability {p r : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α - (r : ℝ))
    (S : Matrix (Fin p) (Fin p) ℝ) : IsProbabilityMeasure (noncentralInputLaw (r := r) α S) := by
  let : IsProbabilityMeasure (bartlettLaw (α - (r : ℝ)) S) := bartlett_law_probability hα S
  unfold noncentralInputLaw
  infer_instance

theorem noncentralInput_polynomial_integrable {p r : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α - (r : ℝ)) (S : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    Integrable (fun x : NoncentralInput p r => (1 + ‖x‖) ^ k) (noncentralInputLaw α S) := by
  apply ((bartlett_polynomial_integrable hα S k).mul_prod
    (gaussian_rows_polynomial_integrable p r k)).mono' (by fun_prop)
  exact ae_of_all _ fun x => by
    have h : 1 + ‖x‖ ≤ (1 + ‖x.1‖) * (1 + ‖x.2‖) := by
      have hn : ‖x‖ ≤ ‖x.1‖ + ‖x.2‖ := by
        rw [Prod.norm_def]
        exact max_le (le_add_of_nonneg_right (norm_nonneg _))
          (le_add_of_nonneg_left (norm_nonneg _))
      nlinarith [norm_nonneg x.1, norm_nonneg x.2, mul_nonneg (norm_nonneg x.1) (norm_nonneg x.2)]
    rw [Real.norm_of_nonneg (by positivity)]
    exact (pow_le_pow_left₀ (by positivity) h k).trans_eq (mul_pow _ _ _)

theorem noncentralInput_real_power_integrable {p r : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α - (r : ℝ)) (S : Matrix (Fin p) (Fin p) ℝ) (β : ℝ) :
    Integrable (fun x : NoncentralInput p r => (1 + ‖x‖) ^ β) (noncentralInputLaw α S) := by
  let k := ⌈β⌉₊
  have hn : Measurable (fun x : NoncentralInput p r => ‖x‖) :=
    measurable_norm (α := (Fin p → Fin p → ℝ) ×
      (Fin r → EuclideanSpace ℝ (Fin p)))
  have hm : Measurable (fun x : NoncentralInput p r => (1 + ‖x‖) ^ β) :=
    (measurable_const.add hn).pow_const β
  apply (noncentralInput_polynomial_integrable hα S k).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) (Nat.le_ceil β)

theorem noncentralValue_polynomial_bound {p r : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (M : Fin r → EuclideanSpace ℝ (Fin p)) (x : NoncentralInput p r) :
    1 + ‖noncentralWishartValue S M x‖ ≤
      (1 + noncentralGrowthConstant S M) * (1 + ‖x‖) ^ (2 : ℕ) := by
  have h := noncentralWishartValue_norm_bound S M x
  have hC : 0 ≤ noncentralGrowthConstant S M := by unfold noncentralGrowthConstant; positivity
  have hx₁ := norm_fst_le x
  have hx₂ := norm_snd_le x
  have hz : (1 + ‖x.2‖) ^ 2 ≤ (1 + ‖x‖) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hp : 1 + ‖x‖ ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
  nlinarith [mul_le_mul_of_nonneg_left hz hC]

noncomputable def noncentralMeanExpectation {p r : ℕ} (α : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (g : Matrix (Fin p) (Fin p) ℝ → ℝ)
    (M : Fin r → EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∫ W, g W ∂(noncentralWishartLaw α S M)

theorem noncentralMeanExpectation_input {p r : ℕ} (α : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) {g : Matrix (Fin p) (Fin p) ℝ → ℝ} (hg : Measurable g)
    (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    noncentralMeanExpectation α S g M =
      ∫ x, g (noncentralWishartValue S M x) ∂(noncentralInputLaw α S) := by
  unfold noncentralMeanExpectation noncentralWishartLaw
  rw [integral_map (measurable_noncentralWishartValue S M).aemeasurable hg.aestronglyMeasurable]
  rfl

theorem noncentralMeanExpectation_continuous {p r : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α - (r : ℝ)) (S : Matrix (Fin p) (Fin p) ℝ)
    {g : Matrix (Fin p) (Fin p) ℝ → ℝ} (hg : Continuous g)
    {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hgB : ∀ W, ‖g W‖ ≤ C * (1 + ‖W‖) ^ β) :
    Continuous (noncentralMeanExpectation (r := r) α S g) := by
  have hgm : Measurable g := Continuous.measurable (α := Fin p → Fin p → ℝ) hg
  have he : noncentralMeanExpectation (r := r) α S g =
      fun M => ∫ x, g (noncentralWishartValue S M x) ∂(noncentralInputLaw α S) := by
    funext M
    exact noncentralMeanExpectation_input α S hgm M
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro M₀
  let D := (r : ℝ) * ((p : ℝ) * ‖CFC.sqrt S‖ + ‖M₀‖ + 1) ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbound : ∀ᶠ M in 𝓝 M₀, ∀ᵐ x ∂(noncentralInputLaw (r := r) α S),
      ‖g (noncentralWishartValue S M x)‖ ≤ C * (1 + D) ^ β * (1 + ‖x‖) ^ (2 * β) := by
    filter_upwards [Metric.ball_mem_nhds M₀ zero_lt_one] with M hM
    exact ae_of_all _ fun x => by
      have hm : ‖M‖ ≤ ‖M₀‖ + 1 := by
        have ht := norm_le_norm_add_norm_sub' M M₀
        have hd : ‖M - M₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hM
        linarith
      have hc : noncentralGrowthConstant S M ≤ D := by
        unfold noncentralGrowthConstant D
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg r)
        apply pow_le_pow_left₀ (by positivity)
        linarith
      have hx := noncentralValue_polynomial_bound S M x
      calc
        _ ≤ C * (1 + ‖noncentralWishartValue S M x‖) ^ β := hgB _
        _ ≤ C * ((1 + D) * (1 + ‖x‖) ^ 2) ^ β :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
            (hx.trans (by gcongr)) hβ) hC
        _ = _ := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            ← Real.rpow_natCast_mul (by positivity) 2]
          norm_num only [Nat.cast_ofNat]
          ring
  apply continuousAt_of_dominated
    (Eventually.of_forall fun M : Fin r → EuclideanSpace ℝ (Fin p) =>
      (hgm.comp (measurable_noncentralWishartValue S M)).aestronglyMeasurable)
    hbound ((noncentralInput_real_power_integrable hα S (2 * β)).const_mul (C * (1 + D) ^ β))
  exact ae_of_all _ fun x => by
    apply hg.continuousAt.comp
    dsimp [noncentralWishartValue, gaussianMeanGram]
    fun_prop

noncomputable def meanRowsCLM (p r : ℕ) :
    Matrix (Fin r) (Fin p) ℝ →L[ℝ] (Fin r → EuclideanSpace ℝ (Fin p)) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun R i => WithLp.toLp 2 (R i)
    map_add' := by intro R T; ext i j; rfl
    map_smul' := by intro c R; ext i j; rfl }

open scoped Matrix.Norms.L2Operator in
theorem matrix_sqrt_continuousOn_positive {r : ℕ} :
    ContinuousOn (CFC.sqrt : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ)
      {W | W.PosDef} :=
  CFC.continuousOn_sqrt.mono fun _W hW => hW.posSemidef.nonneg

open scoped Matrix.Norms.L2Operator in
theorem matrix_sqrt_measurable {r : ℕ} :
    Measurable (CFC.sqrt : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ) :=
  CFC.measurable_sqrt

theorem covarianceMeanRows_continuousOn {p r : ℕ} (K : Matrix (Fin r) (Fin p) ℝ) :
    ContinuousOn (fun W : Matrix (Fin r) (Fin r) ℝ => covarianceMeanRows W K) {W | W.PosDef} := by
  have he : (fun W : Matrix (Fin r) (Fin r) ℝ => covarianceMeanRows W K) =
      fun W => meanRowsCLM p r ((CFC.sqrt W).transpose * K) := rfl
  rw [he]
  have hc : Continuous (fun R : Matrix (Fin r) (Fin r) ℝ => meanRowsCLM p r (R.transpose * K)) := by
    fun_prop
  exact hc.comp_continuousOn matrix_sqrt_continuousOn_positive

theorem covarianceMeanRows_measurable {p r : ℕ} (K : Matrix (Fin r) (Fin p) ℝ) :
    Measurable (fun W : Matrix (Fin r) (Fin r) ℝ => covarianceMeanRows W K) := by
  change Measurable (fun W : Matrix (Fin r) (Fin r) ℝ =>
    meanRowsCLM p r ((CFC.sqrt W).transpose * K))
  have hc : Continuous (fun R : Fin r → Fin r → ℝ =>
      meanRowsCLM p r (Matrix.transpose R * K)) := by fun_prop
  exact (Continuous.measurable (α := Fin r → Fin r → ℝ) hc).comp
    (matrix_sqrt_measurable (r := r))

namespace BlockPartition

theorem determinantProduct_continuous {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) : Continuous (P.determinantProduct ν) := by
  unfold determinantProduct determinantPower block
  apply continuous_finsetProd
  intro j _
  have hs : Continuous (fun W : Matrix (Fin p) (Fin p) ℝ =>
      W.submatrix (P.inclusion j) (P.inclusion j)) := by fun_prop
  exact (Real.continuous_rpow_const (hν j)).comp hs.matrix_det

theorem noncentralProductResponse_continuousOn {p r d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {α : ℝ}
    (hα : (p : ℝ) - 1 < α - (r : ℝ)) (S : Matrix (Fin p) (Fin p) ℝ)
    (K : Matrix (Fin r) (Fin p) ℝ) :
    ContinuousOn (P.noncentralProductResponse α S K ν) {W | W.PosDef} := by
  have he : P.noncentralProductResponse α S K ν =
      fun W => noncentralMeanExpectation α S (P.determinantProduct ν) (covarianceMeanRows W K) := rfl
  rw [he]
  apply (noncentralMeanExpectation_continuous hα S (P.determinantProduct_continuous ν hν)
    (C := ∏ j, (Fintype.card (Equiv.Perm (Fin (P.size j))) : ℝ) ^ ν j)
    (β := P.productGrowthExponent ν) (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hν j)) ?_).comp_continuousOn
      (covarianceMeanRows_continuousOn K)
  intro W
  simpa only [shiftedDeterminantProduct, determinantProduct, determinantPower, add_zero,
    norm_zero, add_zero, one_pow, mul_one, productGrowthExponent] using
      P.shiftedDeterminantProduct_growth (fun _ => 0) ν hν W

theorem noncentralProductResponse_measurable {p r d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {α : ℝ}
    (hα : (p : ℝ) - 1 < α - (r : ℝ)) (S : Matrix (Fin p) (Fin p) ℝ)
    (K : Matrix (Fin r) (Fin p) ℝ) :
    Measurable (P.noncentralProductResponse α S K ν) := by
  have hc := noncentralMeanExpectation_continuous hα S (P.determinantProduct_continuous ν hν)
    (C := ∏ j, (Fintype.card (Equiv.Perm (Fin (P.size j))) : ℝ) ^ ν j)
    (β := P.productGrowthExponent ν) (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hν j)) (fun W => by
      simpa only [shiftedDeterminantProduct, determinantProduct, determinantPower, add_zero,
        norm_zero, add_zero, one_pow, mul_one, productGrowthExponent] using
          P.shiftedDeterminantProduct_growth (fun _ => 0) ν hν W)
  exact hc.measurable.comp (covarianceMeanRows_measurable K)

theorem noncentralProductResponse_nonneg {p r d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (α : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) (K : Matrix (Fin r) (Fin p) ℝ)
    (W : Matrix (Fin r) (Fin r) ℝ) : 0 ≤ P.noncentralProductResponse α S K ν W :=
  integral_nonneg_of_ae ((noncentralWishart_positiveSemidefinite α S (covarianceMeanRows W K)).mono
    fun _B hB => P.determinantProduct_nonneg ν hB)

end BlockPartition
end ResearchMain.WishartBlocks
