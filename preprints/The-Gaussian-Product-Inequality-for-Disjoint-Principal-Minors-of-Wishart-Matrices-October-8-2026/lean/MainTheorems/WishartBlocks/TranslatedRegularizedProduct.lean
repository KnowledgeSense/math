import MainTheorems.WishartBlocks.PolynomialTestODE

namespace ResearchMain.WishartBlocks

open Matrix MeasureTheory
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise ContDiff

namespace BlockPartition

noncomputable def translatedRegularizedProduct {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε : ℝ) (K : Matrix (Fin p) (Fin p) ℝ) (x : MatrixEuclidean p) : ℂ :=
  P.smoothProductEuclidean ν ε (x + matrixCoordinates p K)

theorem translatedRegularizedProduct_contDiff {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) (K : Matrix (Fin p) (Fin p) ℝ) :
    ContDiff ℝ ∞ (P.translatedRegularizedProduct ν ε K) :=
  (P.smoothProductEuclidean_contDiff ν hε).comp (contDiff_id.add contDiff_const)

theorem translatedRegularizedProduct_jet {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε : ℝ) (K W : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    iteratedFDeriv ℝ k (P.translatedRegularizedProduct ν ε K) (matrixCoordinates p W) =
      iteratedFDeriv ℝ k (P.smoothProductEuclidean ν ε) (matrixCoordinates p (W + K)) := by
  unfold translatedRegularizedProduct
  rw [iteratedFDeriv_comp_add_right, map_add]

theorem translatedRegularizedProduct_jet_bound {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε : ℝ} (hε : 0 < ε)
    {K : Matrix (Fin p) (Fin p) ℝ} (hK : K.PosSemidef)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) {k : ℕ} (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (P.translatedRegularizedProduct ν ε K) (matrixCoordinates p W)‖ ≤
      (P.regularizedJetConstant ν ε k *
        (∏ j, (Fintype.card (Equiv.Perm (Fin (P.size j))) *
          (1 + ‖P.block K j + ε • 1‖) ^ P.size j) ^ ν j)) *
            (1 + ‖W‖) ^ P.productGrowthExponent ν := by
  rw [P.translatedRegularizedProduct_jet]
  apply (P.smoothProductEuclidean_jet_bound ν hε (hW.add hK) hk).trans
  have he : P.shiftedDeterminantProduct (fun _ => ε • 1) ν (W + K) =
      P.shiftedDeterminantProduct (fun j => P.block K j + ε • 1) ν W := by
    unfold shiftedDeterminantProduct block
    simp only [Matrix.submatrix_add, Pi.add_apply, add_assoc]
  rw [he]
  exact (mul_le_mul_of_nonneg_right (P.shiftedDeterminantProduct_growth _ ν hν W)
    (P.regularizedJetConstant_nonneg ν hε _)).trans_eq (by
      dsimp only [productGrowthExponent]
      ring)

noncomputable def translatedRegularizedTest {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε : ℝ} (hε : 0 < ε)
    {K : Matrix (Fin p) (Fin p) ℝ} (hK : K.PosSemidef) : PolynomialPSDTest p where
  toFun := P.translatedRegularizedProduct ν ε K
  smooth := P.translatedRegularizedProduct_contDiff ν hε K
  exponent := P.productGrowthExponent ν
  exponent_nonneg := Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hν j)
  jetConstant := fun k => P.regularizedJetConstant ν ε k *
    ∏ j, (Fintype.card (Equiv.Perm (Fin (P.size j))) * (1 + ‖P.block K j + ε • 1‖) ^ P.size j) ^ ν j
  jetConstant_nonneg := fun k => mul_nonneg (P.regularizedJetConstant_nonneg ν hε k)
    (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (by positivity) _)
  jet_bound := fun k hk W hW => P.translatedRegularizedProduct_jet_bound ν hν hε hK hW hk

theorem translatedRegularizedProduct_first {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε)
    {K W : Matrix (Fin p) (Fin p) ℝ} (hK : K.PosSemidef) (hW : W.PosSemidef)
    (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.IsHermitian) :
    fderiv ℝ (P.translatedRegularizedProduct ν ε K) (matrixCoordinates p W) (matrixCoordinates p H) =
      (P.regularizedProductDirectional ε ν H (W + K) : ℂ) := by
  unfold translatedRegularizedProduct
  rw [fderiv_comp_add_right, ← map_add]
  rw [← ((P.smoothProductEuclidean_contDiff ν hε).differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
    P.smoothProductEuclidean_lineDeriv ν hε
      (by simpa only [coordinatesMatrix_matrixCoordinates] using P.regularizedFloorGap_positive (hW.add hK) hε),
    coordinatesMatrix_matrixCoordinates, coordinatesMatrix_matrixCoordinates,
    symmetricMatrixPart_eq_of_hermitian hH, symmetricMatrixPart_eq_of_hermitian (hW.add hK).1]

theorem translatedRegularizedProduct_second {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε)
    {K W : Matrix (Fin p) (Fin p) ℝ} (hK : K.PosSemidef) (hW : W.PosSemidef)
    (H J : Matrix (Fin p) (Fin p) ℝ) (hH : H.IsHermitian) (hJ : J.IsHermitian) :
    fderiv ℝ (fderiv ℝ (P.translatedRegularizedProduct ν ε K))
        (matrixCoordinates p W) (matrixCoordinates p J) (matrixCoordinates p H) =
      (P.regularizedProductHessian ε ν H J (W + K) : ℂ) := by
  have he : fderiv ℝ (P.translatedRegularizedProduct ν ε K) =
      fun x => fderiv ℝ (P.smoothProductEuclidean ν ε) (x + matrixCoordinates p K) := by
    funext x
    exact fderiv_comp_add_right _
  rw [he, fderiv_comp_add_right, ← map_add, ← smooth_second_lineDeriv (P.smoothProductEuclidean_contDiff ν hε),
    P.smoothProductEuclidean_second_lineDeriv ν hε
      (by simpa only [coordinatesMatrix_matrixCoordinates] using P.regularizedFloorGap_positive (hW.add hK) hε)]
  simp only [coordinatesMatrix_matrixCoordinates,
    symmetricMatrixPart_eq_of_hermitian hH, symmetricMatrixPart_eq_of_hermitian hJ,
    symmetricMatrixPart_eq_of_hermitian (hW.add hK).1]

theorem translatedRegularizedProduct_operator_nonneg {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε q : ℝ} (hε : 0 < ε)
    (hqB : ∀ j, (P.size j : ℝ) + 1 ≤ q) (v : EuclideanSpace ℝ (Fin p))
    {K W : Matrix (Fin p) (Fin p) ℝ} (hK : K.PosSemidef) (hW : W.PosSemidef) :
    0 ≤ (matrixTestOperator (P.translatedRegularizedProduct ν ε K) q v W).re := by
  classical
  let U := fun a : Fin p => fun i : (Σ j, Fin (P.size j)) => CFC.sqrt W (P.index i) a
  let u := fun i : (Σ j, Fin (P.size j)) => v (P.index i)
  have hGram : gramSum U = W.submatrix P.index P.index := by
    rw [← gramSum_submatrix (fun a i => CFC.sqrt W i a) P.index, sqrt_column_gramSum hW]
  have hWA (j : Fin d) : principalBlock (gramSum U) j ≤ P.regularizedBlocks ε (W + K) j := by
    rw [hGram]
    change P.block W j ≤ P.block (W + K) j + ε • 1
    change (P.block (W + K) j + ε • 1 - P.block W j).PosSemidef
    have he : P.block (W + K) j + ε • 1 - P.block W j = P.block K j + ε • 1 := by
      ext i l
      simp only [block, Matrix.submatrix_apply, Matrix.add_apply, Matrix.sub_apply]
      ring
    rw [he]
    exact
      (hK.submatrix (P.inclusion j)).add
        ((Matrix.PosSemidef.one : (1 : Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ).PosSemidef).smul hε.le)
  have h := determinant_product_operator_nonneg (P.regularizedBlocks ε (W + K)) ν q
    (P.regularizedBlocks_posDef (hW.add hK) hε) U u hWA hν hqB
  have he : matrixTestOperator (P.translatedRegularizedProduct ν ε K) q v W =
      ((q * P.regularizedProductDirectional ε ν (Matrix.vecMulVec (fun i => v i) (fun i => v i)) (W + K) +
        2 * ∑ a : Fin p, P.regularizedProductHessian ε ν
          (rankTwoDirection (fun i => CFC.sqrt W i a) (fun i => v i))
          (rankTwoDirection (fun i => CFC.sqrt W i a) (fun i => v i)) (W + K) : ℝ) : ℂ) := by
    unfold matrixTestOperator
    rw [P.translatedRegularizedProduct_first ν hε hK hW _ (by
      simpa only [star_trivial] using (Matrix.posSemidef_vecMulVec_self_star (fun i => v i)).1)]
    simp_rw [P.translatedRegularizedProduct_second ν hε hK hW _ _ (rankTwoDirection_isHermitian _ _)
      (rankTwoDirection_isHermitian _ _)]
    push_cast
    rfl
  rw [he, Complex.ofReal_re]
  convert h using 1
  congr 2

theorem translatedRegularizedTest_expectation_actualLaw {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε : ℝ} (hε : 0 < ε)
    {K : Matrix (Fin p) (Fin p) ℝ} (hK : K.PosSemidef)
    (q : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    ((P.translatedRegularizedTest ν hν hε hK).expectation q S v s).re =
      ∫ W, P.shiftedDeterminantProduct (fun j => P.block K j + ε • 1) ν W
        ∂(oneRowWishartLaw q S (s • v)) := by
  have he : (P.translatedRegularizedTest ν hν hε hK).expectation q S v s =
      ∫ W, (P.smoothRegularizedProduct ν ε (W + K) : ℂ) ∂(oneRowWishartLaw q S (s • v)) := by
    have hc : ContDiff ℝ ∞ (fun W : Matrix (Fin p) (Fin p) ℝ =>
        (P.smoothRegularizedProduct ν ε (W + K) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((P.smoothRegularizedProduct_contDiff ν hε).comp
        (contDiff_id.add contDiff_const))
    have hm : Measurable (fun W : Matrix (Fin p) (Fin p) ℝ =>
        (P.smoothRegularizedProduct ν ε (W + K) : ℂ)) :=
      Continuous.measurable (α := Fin p → Fin p → ℝ) hc.continuous
    unfold oneRowWishartLaw
    rw [integral_map (measurable_oneRowWishartValue S (s • v)).aemeasurable hm.aestronglyMeasurable]
    simp only [PolynomialPSDTest.expectation, gaussianMatrixTest, translatedRegularizedTest,
      translatedRegularizedProduct, smoothProductEuclidean, map_add, coordinatesMatrix_matrixCoordinates]
    rfl
  rw [he]
  have hf : (fun W => (P.smoothRegularizedProduct ν ε (W + K) : ℂ)) =ᵐ[
      oneRowWishartLaw q S (s • v)] (fun W => (P.shiftedDeterminantProduct
        (fun j => P.block K j + ε • 1) ν W : ℂ)) := by
    filter_upwards [oneRowWishart_positiveSemidefinite q S (s • v)] with W hW
    rw [P.smoothRegularizedProduct_eq ν hε (hW.add hK)]
    simp only [regularizedBlocks, shiftedDeterminantProduct, block, Matrix.submatrix_add, Pi.add_apply, add_assoc]
  rw [integral_congr_ae hf, integral_complex_ofReal]
  rfl

theorem rankOne_shifted_product_monotone {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {q : ℝ} (hq : (p : ℝ) < q) (hq₁ : 1 < q)
    (hqB : ∀ j, (P.size j : ℝ) + 1 ≤ q) {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    {K : Matrix (Fin p) (Fin p) ℝ} (hK : K.PosSemidef) (v : EuclideanSpace ℝ (Fin p)) :
    MonotoneOn (fun θ => ∫ W, P.shiftedDeterminantProduct (fun j => P.block K j) ν W
      ∂(oneRowWishartLaw q S (Real.sqrt θ • v))) (Set.Ici 0) := by
  intro θ hθ η hη hθη
  apply le_of_tendsto_of_tendsto
    (P.oneRowWishart_regularizedShift_integral_tendsto (fun j => P.block K j) ν hν hq hS (Real.sqrt θ • v))
    (P.oneRowWishart_regularizedShift_integral_tendsto (fun j => P.block K j) ν hν hq hS (Real.sqrt η • v))
  exact Filter.Eventually.of_forall fun N => by
    have h := (P.translatedRegularizedTest ν hν (regularizationScale_pos N) hK).mean_ray_monotone
      hq hq₁ hS v (fun W hW => P.translatedRegularizedProduct_operator_nonneg ν hν
        (regularizationScale_pos N) hqB v hK hW) hθ hη hθη
    change ((P.translatedRegularizedTest ν hν (regularizationScale_pos N) hK).expectation
      q S v (Real.sqrt θ)).re ≤
        ((P.translatedRegularizedTest ν hν (regularizationScale_pos N) hK).expectation
          q S v (Real.sqrt η)).re at h
    rwa [P.translatedRegularizedTest_expectation_actualLaw,
      P.translatedRegularizedTest_expectation_actualLaw] at h

end BlockPartition
end ResearchMain.WishartBlocks

