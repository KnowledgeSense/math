import MainTheorems.WishartBlocks.MeanRowRotations

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder InnerProductSpace

noncomputable def augmentedOneRowLaw {p r : ℕ} (q : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (m : EuclideanSpace ℝ (Fin p))
    (M : Fin r → EuclideanSpace ℝ (Fin p)) : Measure (Matrix (Fin p) (Fin p) ℝ) :=
  ((oneRowWishartLaw q S m).prod
    (Measure.pi fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin p)))).map
      (noncentralWishartValue S M)

theorem augmentedOneRow_probability {p r : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (m : EuclideanSpace ℝ (Fin p))
    (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    IsProbabilityMeasure (augmentedOneRowLaw q S m M) := by
  let : IsProbabilityMeasure (oneRowWishartLaw q S m) := oneRowWishart_probability hq S m
  unfold augmentedOneRowLaw
  infer_instance

theorem augmentedOneRow_positiveSemidefinite {p r : ℕ} (q : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (m : EuclideanSpace ℝ (Fin p))
    (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    ∀ᵐ W ∂(augmentedOneRowLaw q S m M), W.PosSemidef := by
  unfold augmentedOneRowLaw
  rw [ae_map_iff (measurable_noncentralWishartValue S M).aemeasurable
    Matrix.posSemidef_is_closed.measurableSet]
  have hw : ∀ᵐ wz ∂((oneRowWishartLaw q S m).prod
      (Measure.pi fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin p)))),
      wz.1.PosSemidef := Measure.quasiMeasurePreserving_fst.ae
    (oneRowWishart_positiveSemidefinite q S m)
  filter_upwards [hw] with wz hwz
  apply hwz.add
  apply Matrix.posSemidef_sum
  intro i _
  simpa only [gaussianMeanGram, star_trivial] using
    Matrix.posSemidef_vecMulVec_self_star
      (fun j => ((CFC.sqrt S).toEuclideanLin (wz.2 i) + M i) j)

theorem augmentedOneRow_laplace {p r : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    {S T : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hT : T.PosSemidef)
    (m : EuclideanSpace ℝ (Fin p)) (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    ∫ W, Real.exp (-Matrix.trace (T * W)) ∂(augmentedOneRowLaw q S m M) =
      (1 + (2 : ℝ) • (S * T)).det ^ (-(q + (r : ℝ)) / 2) *
        Real.exp (-Matrix.trace
          ((Matrix.vecMulVec (fun i => m i) (fun i => m i) + meanRowGram M) *
            (T * (1 + (2 : ℝ) • (S * T))⁻¹))) := by
  let : IsProbabilityMeasure (oneRowWishartLaw q S m) := oneRowWishart_probability hq S m
  let D := (1 + (2 : ℝ) • (S * T)).det
  have hD : 0 < D := covariance_precision_det_pos hS.posSemidef hT
  have hpow : (Real.sqrt (1 + (2 : ℝ) • (S * T)).det)⁻¹ = D ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    exact (Real.rpow_neg hD.le (1 / 2)).symm
  unfold augmentedOneRowLaw
  rw [integral_map (measurable_noncentralWishartValue S M).aemeasurable
    (continuous_exp_trace_mul T).measurable.aestronglyMeasurable]
  simp_rw [noncentralWishartValue, Matrix.mul_add, Matrix.trace_add, Matrix.mul_sum,
    Matrix.trace_sum, neg_add, Real.exp_add, ← Finset.sum_neg_distrib,
    Real.exp_sum, trace_gaussianMeanGram]
  rw [integral_prod_mul (fun W : Matrix (Fin p) (Fin p) ℝ => Real.exp (-Matrix.trace (T * W)))
    (fun z : Fin r → EuclideanSpace ℝ (Fin p) =>
      ∏ i, Real.exp (-⟪(CFC.sqrt S).toEuclideanLin (z i) + M i,
        T.toEuclideanLin ((CFC.sqrt S).toEuclideanLin (z i) + M i)⟫_ℝ)),
    oneRowWishart_laplace hq hS hT,
    integral_fintype_prod_eq_prod
      (f := fun i z => Real.exp (-⟪(CFC.sqrt S).toEuclideanLin z + M i,
        T.toEuclideanLin ((CFC.sqrt S).toEuclideanLin z + M i)⟫_ℝ))]
  simp_rw [gaussian_affine_laplace hS hT, hpow]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.rpow_natCast, ← Real.rpow_mul hD.le,
    ← Real.exp_sum, Finset.sum_neg_distrib, ← meanRowGram_trace,
    Matrix.add_mul, Matrix.trace_add, neg_add, Real.exp_add,
    Matrix.trace_mul_comm (Matrix.vecMulVec (fun i => m i) (fun i => m i)),
    trace_vectorGram]
  change D ^ (-q / 2) * _ * _ = D ^ ((-q + -(r : ℝ)) / 2) * _
  have hp : D ^ ((-q + -(r : ℝ)) / 2) = D ^ (-q / 2) * D ^ (-(r : ℝ) / 2) := by
    rw [← Real.rpow_add hD]
    congr 1
    ring
  have hr : D ^ ((-(1 / 2 : ℝ)) * (r : ℝ)) = D ^ (-(r : ℝ) / 2) := by
    congr 1
    ring
  rw [hp, hr]
  ring

theorem noncentralWishart_cons_row {p r : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (m : EuclideanSpace ℝ (Fin p)) (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    augmentedOneRowLaw q S m M =
      noncentralWishartLaw (q + (r : ℝ)) S (Fin.cons m M) := by
  have hα : (p : ℝ) - 1 < (q + (r : ℝ)) - ((r + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  let : IsProbabilityMeasure (augmentedOneRowLaw q S m M) :=
    augmentedOneRow_probability hq S m M
  let : IsProbabilityMeasure (noncentralWishartLaw (q + (r : ℝ)) S (Fin.cons m M)) :=
    noncentralWishart_probability hα S _
  apply matrix_measure_eq_of_positive_laplace
    (augmentedOneRow_positiveSemidefinite q S m M)
    (noncentralWishart_positiveSemidefinite (q + (r : ℝ)) S _)
  intro T hT
  rw [augmentedOneRow_laplace hq hS hT, noncentralWishart_laplace hα hS hT,
    meanRowGram_cons]

theorem oneRowWishart_neg_mean {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (m : EuclideanSpace ℝ (Fin p)) :
    oneRowWishartLaw q S (-m) = oneRowWishartLaw q S m := by
  let : IsProbabilityMeasure (oneRowWishartLaw q S (-m)) := oneRowWishart_probability hq S _
  let : IsProbabilityMeasure (oneRowWishartLaw q S m) := oneRowWishart_probability hq S m
  apply matrix_measure_eq_of_positive_laplace
    (oneRowWishart_positiveSemidefinite q S _) (oneRowWishart_positiveSemidefinite q S m)
  intro T hT
  rw [oneRowWishart_laplace hq hS hT, oneRowWishart_laplace hq hS hT]
  simp only [map_neg, inner_neg_left, inner_neg_right, neg_neg]

end ResearchMain.WishartBlocks
