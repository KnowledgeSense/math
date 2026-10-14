import MainTheorems.WishartBlocks.GaussianMeanCurve
import MainTheorems.WishartBlocks.CoordinateInputNorm

namespace ResearchMain.WishartBlocks

open MeasureTheory Matrix
open scoped BigOperators InnerProductSpace MatrixOrder Matrix.Norms.Elementwise ContDiff

theorem oneRowWishartValue_local_norm_bound {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) {t : ℝ} (ht : |t - s| < 1)
    (x : OneRowInput p) :
    ‖oneRowWishartValue S (t • v) x‖ ≤ oneRowMatrixBound S v (|s| + 1) * (1 + ‖x‖) ^ 2 := by
  have ht' : |t| ≤ |s| + 1 := by
    have h := abs_add_le (t - s) s
    have he : t - s + s = t := by ring
    rw [he] at h
    linarith
  apply (oneRowWishartValue_norm_bound S v t x).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  unfold oneRowMatrixBound
  rw [abs_of_nonneg (by positivity : 0 ≤ |s| + 1)]
  gcongr

theorem oneRowInput_complex_growth_integrable {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) {f : OneRowInput p → ℂ} (hf : Measurable f)
    {C β : ℝ} (hC : 0 ≤ C) (hB : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ β) :
    Integrable f (oneRowInputLaw q S) := by
  apply (integrable_norm_iff hf.aestronglyMeasurable).mp
  exact oneRowInput_real_growth_integrable hq S hf.norm hC (fun x => by
    simpa only [Real.norm_of_nonneg (norm_nonneg (f x))] using hB x)

theorem gaussianMatrixTest_measurable {p : ℕ} {f : MatrixEuclidean p → ℂ}
    (hf : ContDiff ℝ ∞ f) (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : Measurable (gaussianMatrixTest f S v s) :=
  hf.continuous.measurable.comp
    ((matrixCoordinates p).continuous.measurable.comp (measurable_oneRowWishartValue S (s • v)))

theorem measurable_oneRowMatrixFirst {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : Measurable (oneRowMatrixFirst S v s) := by
  have hy : Continuous (oneRowGaussianVector S v s) :=
    ((CFC.sqrt S).toEuclideanLin.toContinuousLinearMap.continuous.comp continuous_snd).add
      continuous_const
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun x : OneRowInput p =>
    oneRowGaussianVector S v s x i * v j + v i * oneRowGaussianVector S v s x j)
  have hi := (PiLp.continuous_apply (p := 2) (fun _ : Fin p => ℝ) i).measurable.comp hy.measurable
  have hj := (PiLp.continuous_apply (p := 2) (fun _ : Fin p => ℝ) j).measurable.comp hy.measurable
  exact (hi.fun_mul measurable_const).add (measurable_const.fun_mul hj)

theorem gaussianMatrixTestFirst_measurable {p : ℕ} {f : MatrixEuclidean p → ℂ}
    (hf : ContDiff ℝ ∞ f) (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : Measurable (gaussianMatrixTestFirst f S v s) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdf : Continuous (fderiv ℝ f) := hfd.continuous
  have hW := (matrixCoordinates p).continuous.measurable.comp
    (measurable_oneRowWishartValue S (s • v))
  have hM := (matrixCoordinates p).continuous.measurable.comp (measurable_oneRowMatrixFirst S v s)
  change Measurable (fun x : OneRowInput p =>
    fderiv ℝ f (matrixCoordinates p (oneRowWishartValue S (s • v) x))
      (matrixCoordinates p (oneRowMatrixFirst S v s x)))
  fun_prop

theorem gaussianMatrixTestSecond_measurable {p : ℕ} {f : MatrixEuclidean p → ℂ}
    (hf : ContDiff ℝ ∞ f) (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : Measurable (gaussianMatrixTestSecond f S v s) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hd : Continuous (fderiv ℝ f) := hdf.continuous
  have hfdd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hdf.fderiv_right (by simp)
  have hdd : Continuous (fderiv ℝ (fderiv ℝ f)) := hfdd.continuous
  have hW := (matrixCoordinates p).continuous.measurable.comp
    (measurable_oneRowWishartValue S (s • v))
  have hM := (matrixCoordinates p).continuous.measurable.comp (measurable_oneRowMatrixFirst S v s)
  change Measurable (fun x : OneRowInput p =>
    fderiv ℝ (fderiv ℝ f) (matrixCoordinates p (oneRowWishartValue S (s • v) x))
        (matrixCoordinates p (oneRowMatrixFirst S v s x))
        (matrixCoordinates p (oneRowMatrixFirst S v s x)) +
      fderiv ℝ f (matrixCoordinates p (oneRowWishartValue S (s • v) x))
        (matrixCoordinates p (oneRowMatrixSecond v)))
  fun_prop

namespace BlockPartition

noncomputable def productGrowthExponent {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) : ℝ := ∑ j, (P.size j : ℝ) * ν j

noncomputable def regularizedGrowthConstant {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε : ℝ) : ℝ :=
  ∏ j, (Fintype.card (Equiv.Perm (Fin (P.size j))) *
    (1 + ‖(ε • (1 : Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ))‖) ^ P.size j) ^ ν j

noncomputable def localProductConstant {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : ℝ :=
  P.regularizedGrowthConstant ν ε *
    (1 + oneRowMatrixBound S v (|s| + 1)) ^ P.productGrowthExponent ν

noncomputable def localFirstMatrixConstant {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : ℝ :=
  2 * matrixCoordinatesOperatorNorm p * oneRowGaussianBound S v s * ‖v‖

noncomputable def secondMatrixConstant {p : ℕ} (v : EuclideanSpace ℝ (Fin p)) : ℝ :=
  2 * matrixCoordinatesOperatorNorm p * ‖v‖ ^ 2

theorem localFirstMatrixConstant_nonneg {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : 0 ≤ localFirstMatrixConstant S v s := by
  have h := oneRowGaussianBound_nonneg S v s
  have hN := matrixCoordinatesOperatorNorm_nonneg p
  unfold localFirstMatrixConstant
  positivity

theorem secondMatrixConstant_nonneg {p : ℕ} (v : EuclideanSpace ℝ (Fin p)) :
    0 ≤ secondMatrixConstant v := by
  have hN := matrixCoordinatesOperatorNorm_nonneg p
  unfold secondMatrixConstant
  positivity

theorem localProductConstant_nonneg {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : 0 ≤ P.localProductConstant ν ε S v s := by
  unfold localProductConstant regularizedGrowthConstant
  apply mul_nonneg (Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (by positivity) _)
  exact Real.rpow_nonneg (by dsimp [oneRowMatrixBound]; positivity) _

theorem local_regularizedProduct_bound {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) (ε : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ)
    {t : ℝ} (ht : |t - s| < 1) (x : OneRowInput p) :
    ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν (oneRowWishartValue S (t • v) x)‖ ≤
      P.localProductConstant ν ε S v s * (1 + ‖x‖) ^ (2 * P.productGrowthExponent ν) := by
  have hβ : 0 ≤ P.productGrowthExponent ν :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hν j)
  have hC : 0 ≤ P.regularizedGrowthConstant ν ε :=
    Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (by positivity) _
  have hW : 1 + ‖oneRowWishartValue S (t • v) x‖ ≤
      (1 + oneRowMatrixBound S v (|s| + 1)) * (1 + ‖x‖) ^ 2 := by
    have h := oneRowWishartValue_local_norm_bound S v s ht x
    nlinarith [norm_nonneg x]
  calc
    _ ≤ P.regularizedGrowthConstant ν ε *
        (1 + ‖oneRowWishartValue S (t • v) x‖) ^ P.productGrowthExponent ν :=
      P.shiftedDeterminantProduct_growth _ ν hν _
    _ ≤ P.regularizedGrowthConstant ν ε *
        ((1 + oneRowMatrixBound S v (|s| + 1)) * (1 + ‖x‖) ^ 2) ^ P.productGrowthExponent ν :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hW hβ) hC
    _ = _ := by
      rw [Real.mul_rpow (by dsimp [oneRowMatrixBound]; positivity) (by positivity),
        ← Real.rpow_natCast_mul (by positivity) 2]
      dsimp only [localProductConstant]
      norm_num only [Nat.cast_ofNat]
      ring

theorem first_matrix_local_bound {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) {t : ℝ} (ht : |t - s| < 1) (x : OneRowInput p) :
    ‖matrixCoordinates p (oneRowMatrixFirst S v t x)‖ ≤
      localFirstMatrixConstant S v s * (1 + ‖x‖) := by
  have hN := matrixCoordinatesOperatorNorm_nonneg p
  apply (matrixCoordinates_norm_bound _).trans
  calc
    _ ≤ matrixCoordinatesOperatorNorm p *
        (2 * (oneRowGaussianBound S v s * (1 + ‖x‖)) * ‖v‖) := by
      apply mul_le_mul_of_nonneg_left _ hN
      apply (oneRowMatrixFirst_norm_bound S v t x).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (oneRowGaussianVector_local_bound S v s ht x)
          (by norm_num)) (norm_nonneg v)
    _ = _ := by unfold localFirstMatrixConstant; ring

theorem second_matrix_bound {p : ℕ} (v : EuclideanSpace ℝ (Fin p)) :
    ‖matrixCoordinates p (oneRowMatrixSecond v)‖ ≤ secondMatrixConstant v := by
  apply (matrixCoordinates_norm_bound _).trans
  simpa only [secondMatrixConstant, mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left (oneRowMatrixSecond_norm_bound v)
      (matrixCoordinatesOperatorNorm_nonneg p)

theorem gaussianProductFirst_local_bound {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε : ℝ} (hε : 0 < ε)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ)
    {t : ℝ} (ht : |t - s| < 1) {x : OneRowInput p} (hx : x.1.PosSemidef) :
    ‖gaussianMatrixTestFirst (P.smoothProductEuclidean ν ε) S v t x‖ ≤
      (P.localProductConstant ν ε S v s * P.regularizedJetConstant ν ε 1 *
        localFirstMatrixConstant S v s) * (1 + ‖x‖) ^ (2 * P.productGrowthExponent ν + 1) := by
  have hW := oneRowWishartValue_positive S v t hx
  have hJ := P.smoothProductEuclidean_jet_bound ν hε hW (by norm_num : 1 ≤ 2)
  have hA := P.localProductConstant_nonneg ν ε S v s
  have hK := P.regularizedJetConstant_nonneg ν hε 1
  have hD := localFirstMatrixConstant_nonneg S v s
  have hJ' := hJ.trans (mul_le_mul_of_nonneg_right
    (P.local_regularizedProduct_bound ν hν ε S v s ht x) hK)
  apply (gaussianMatrixTestFirst_jet_bound _ S v t x).trans
  calc
    _ ≤ (P.localProductConstant ν ε S v s * (1 + ‖x‖) ^ (2 * P.productGrowthExponent ν) *
        P.regularizedJetConstant ν ε 1) * (localFirstMatrixConstant S v s * (1 + ‖x‖)) := by
      apply mul_le_mul hJ'
        (first_matrix_local_bound S v s ht x) (norm_nonneg _) (by positivity)
    _ = _ := by rw [Real.rpow_add (by positivity), Real.rpow_one]; ring

theorem gaussianProductSecond_local_bound {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε : ℝ} (hε : 0 < ε)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ)
    {t : ℝ} (ht : |t - s| < 1) {x : OneRowInput p} (hx : x.1.PosSemidef) :
    ‖gaussianMatrixTestSecond (P.smoothProductEuclidean ν ε) S v t x‖ ≤
      (P.localProductConstant ν ε S v s *
        (P.regularizedJetConstant ν ε 2 * localFirstMatrixConstant S v s ^ 2 +
          P.regularizedJetConstant ν ε 1 * secondMatrixConstant v)) *
            (1 + ‖x‖) ^ (2 * P.productGrowthExponent ν + 2) := by
  have hW := oneRowWishartValue_positive S v t hx
  have hJ₁ := P.smoothProductEuclidean_jet_bound ν hε hW (by norm_num : 1 ≤ 2)
  have hJ₂ := P.smoothProductEuclidean_jet_bound ν hε hW (by norm_num : 2 ≤ 2)
  have hA := P.localProductConstant_nonneg ν ε S v s
  have hK₁ := P.regularizedJetConstant_nonneg ν hε 1
  have hK₂ := P.regularizedJetConstant_nonneg ν hε 2
  have hD := localFirstMatrixConstant_nonneg S v s
  have hE := secondMatrixConstant_nonneg v
  have hg := P.local_regularizedProduct_bound ν hν ε S v s ht x
  have hM := first_matrix_local_bound S v s ht x
  have hJ₁' := hJ₁.trans (mul_le_mul_of_nonneg_right hg hK₁)
  have hJ₂' := hJ₂.trans (mul_le_mul_of_nonneg_right hg hK₂)
  have h2 : 1 ≤ (1 + ‖x‖) ^ (2 : ℕ) := by nlinarith [norm_nonneg x]
  apply (gaussianMatrixTestSecond_jet_bound _ S v t x).trans
  calc
    _ ≤ (P.localProductConstant ν ε S v s * (1 + ‖x‖) ^ (2 * P.productGrowthExponent ν) *
        P.regularizedJetConstant ν ε 2) * (localFirstMatrixConstant S v s * (1 + ‖x‖)) ^ 2 +
      (P.localProductConstant ν ε S v s * (1 + ‖x‖) ^ (2 * P.productGrowthExponent ν) *
        P.regularizedJetConstant ν ε 1) * secondMatrixConstant v := by
      apply add_le_add
      · exact mul_le_mul hJ₂' (pow_le_pow_left₀ (norm_nonneg _) hM 2)
          (sq_nonneg _) (by positivity)
      · exact mul_le_mul hJ₁' (second_matrix_bound v) (norm_nonneg _) (by positivity)
    _ ≤ (P.localProductConstant ν ε S v s * (1 + ‖x‖) ^ (2 * P.productGrowthExponent ν) *
        P.regularizedJetConstant ν ε 2) * (localFirstMatrixConstant S v s * (1 + ‖x‖)) ^ 2 +
      (P.localProductConstant ν ε S v s * (1 + ‖x‖) ^ (2 * P.productGrowthExponent ν) *
        P.regularizedJetConstant ν ε 1) * secondMatrixConstant v * (1 + ‖x‖) ^ (2 : ℕ) := by
      apply add_le_add le_rfl
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h2
        (by positivity : 0 ≤
          (P.localProductConstant ν ε S v s * (1 + ‖x‖) ^ (2 * P.productGrowthExponent ν) *
            P.regularizedJetConstant ν ε 1) * secondMatrixConstant v)
    _ = _ := by rw [Real.rpow_add (by positivity), Real.rpow_two]; ring

end BlockPartition
end ResearchMain.WishartBlocks
