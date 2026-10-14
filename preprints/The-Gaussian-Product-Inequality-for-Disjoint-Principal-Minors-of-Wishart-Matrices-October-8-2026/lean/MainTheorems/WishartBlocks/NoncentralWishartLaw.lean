import MainTheorems.WishartBlocks.RankOneWishartLaw

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder InnerProductSpace

noncomputable def meanRowGram {p r : ℕ} (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ :=
  ∑ i, Matrix.vecMulVec (fun j => M i j) (fun j => M i j)

noncomputable def noncentralWishartValue {p r : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (M : Fin r → EuclideanSpace ℝ (Fin p))
    (wz : Matrix (Fin p) (Fin p) ℝ × (Fin r → EuclideanSpace ℝ (Fin p))) :
    Matrix (Fin p) (Fin p) ℝ := wz.1 + ∑ i, gaussianMeanGram S (M i) (wz.2 i)

noncomputable def noncentralWishartLaw {p r : ℕ} (α : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    Measure (Matrix (Fin p) (Fin p) ℝ) :=
  ((bartlettLaw (α - (r : ℝ)) S).prod
    (Measure.pi fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin p)))).map
      (noncentralWishartValue S M)

theorem measurable_noncentralWishartValue {p r : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (M : Fin r → EuclideanSpace ℝ (Fin p)) : Measurable (noncentralWishartValue S M) := by
  let : MeasurableAdd₂ (Matrix (Fin p) (Fin p) ℝ) :=
    inferInstanceAs (MeasurableAdd₂ (Fin p → Fin p → ℝ))
  unfold noncentralWishartValue
  exact measurable_fst.add (Finset.measurable_fun_sum Finset.univ (fun i _ =>
    (measurable_gaussianMeanGram S (M i)).comp ((measurable_pi_apply i).comp measurable_snd)))

theorem noncentralWishart_probability {p r : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α - (r : ℝ))
    (S : Matrix (Fin p) (Fin p) ℝ) (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    IsProbabilityMeasure (noncentralWishartLaw α S M) := by
  let : IsProbabilityMeasure (bartlettLaw (α - (r : ℝ)) S) := bartlett_law_probability hα S
  unfold noncentralWishartLaw
  infer_instance

theorem noncentralWishart_positiveSemidefinite {p r : ℕ} (α : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    ∀ᵐ W ∂(noncentralWishartLaw α S M), W.PosSemidef := by
  unfold noncentralWishartLaw
  rw [ae_map_iff (measurable_noncentralWishartValue S M).aemeasurable
    Matrix.posSemidef_is_closed.measurableSet]
  have hw : ∀ᵐ wz ∂((bartlettLaw (α - (r : ℝ)) S).prod
      (Measure.pi fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin p)))),
      wz.1.PosSemidef :=
    Measure.quasiMeasurePreserving_fst.ae
      (bartlettLaw_positiveSemidefinite (α - (r : ℝ)) S)
  filter_upwards [hw] with wz hwz
  apply hwz.add
  apply Matrix.posSemidef_sum
  intro i _
  simpa only [gaussianMeanGram, star_trivial] using
    Matrix.posSemidef_vecMulVec_self_star
      (fun j => ((CFC.sqrt S).toEuclideanLin (wz.2 i) + M i) j)

theorem meanRowGram_trace {p r : ℕ} (M : Fin r → EuclideanSpace ℝ (Fin p))
    (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (meanRowGram M * A) = ∑ i, ⟪M i, A.toEuclideanLin (M i)⟫_ℝ := by
  rw [meanRowGram, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.trace_mul_comm, trace_vectorGram]

theorem noncentralWishart_laplace {p r : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α - (r : ℝ)) {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosSemidef) (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    ∫ W, Real.exp (-Matrix.trace (T * W)) ∂(noncentralWishartLaw α S M) =
      (1 + (2 : ℝ) • (S * T)).det ^ (-α / 2) *
        Real.exp (-Matrix.trace (meanRowGram M * (T * (1 + (2 : ℝ) • (S * T))⁻¹))) := by
  let : IsProbabilityMeasure (bartlettLaw (α - (r : ℝ)) S) := bartlett_law_probability hα S
  have hD := covariance_precision_det_pos hS.posSemidef hT
  unfold noncentralWishartLaw
  rw [integral_map (measurable_noncentralWishartValue S M).aemeasurable
    (continuous_exp_trace_mul T).measurable.aestronglyMeasurable]
  simp_rw [noncentralWishartValue, Matrix.mul_add, Matrix.trace_add, Matrix.mul_sum,
    Matrix.trace_sum, neg_add, Real.exp_add, ← Finset.sum_neg_distrib, Real.exp_sum,
    trace_gaussianMeanGram]
  rw [integral_prod_mul (fun W : Matrix (Fin p) (Fin p) ℝ => Real.exp (-Matrix.trace (T * W)))
    (fun z : Fin r → EuclideanSpace ℝ (Fin p) =>
      ∏ i, Real.exp (-⟪(CFC.sqrt S).toEuclideanLin (z i) + M i,
        T.toEuclideanLin ((CFC.sqrt S).toEuclideanLin (z i) + M i)⟫_ℝ)),
    bartlettLaw_laplace hα hS.posSemidef hT,
    integral_fintype_prod_eq_prod
      (f := fun i z => Real.exp (-⟪(CFC.sqrt S).toEuclideanLin z + M i,
        T.toEuclideanLin ((CFC.sqrt S).toEuclideanLin z + M i)⟫_ℝ))]
  simp_rw [gaussian_affine_laplace hS hT, Real.sqrt_eq_rpow, ← Real.rpow_neg hD.le]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.rpow_natCast, ← Real.rpow_mul hD.le,
    ← Real.exp_sum, Finset.sum_neg_distrib, ← meanRowGram_trace,
    ← mul_assoc, ← Real.rpow_add hD]
  congr 1
  congr 1
  ring

theorem noncentralWishart_meanGram_eq {p r s : ℕ} {α : ℝ}
    (hαr : (p : ℝ) - 1 < α - (r : ℝ)) (hαs : (p : ℝ) - 1 < α - (s : ℝ))
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (M : Fin r → EuclideanSpace ℝ (Fin p)) (N : Fin s → EuclideanSpace ℝ (Fin p))
    (hMN : meanRowGram M = meanRowGram N) :
    noncentralWishartLaw α S M = noncentralWishartLaw α S N := by
  let : IsProbabilityMeasure (noncentralWishartLaw α S M) := noncentralWishart_probability hαr S M
  let : IsProbabilityMeasure (noncentralWishartLaw α S N) := noncentralWishart_probability hαs S N
  apply matrix_measure_eq_of_positive_laplace
    (noncentralWishart_positiveSemidefinite α S M) (noncentralWishart_positiveSemidefinite α S N)
  intro T hT
  rw [noncentralWishart_laplace hαr hS hT, noncentralWishart_laplace hαs hS hT, hMN]

theorem noncentralWishart_zero_mean {p r : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α - (r : ℝ))
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) :
    noncentralWishartLaw α S (fun _ : Fin r => 0) = bartlettLaw α S := by
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  have hαp : (p : ℝ) - 1 < α := by linarith
  let : IsProbabilityMeasure (noncentralWishartLaw α S (fun _ : Fin r => 0)) :=
    noncentralWishart_probability hα S _
  let : IsProbabilityMeasure (bartlettLaw α S) := bartlett_law_probability hαp S
  apply matrix_measure_eq_of_positive_laplace
    (noncentralWishart_positiveSemidefinite α S _) (bartlettLaw_positiveSemidefinite α S)
  intro T hT
  rw [noncentralWishart_laplace hα hS hT, bartlettLaw_laplace hαp hS.posSemidef hT]
  have hz : meanRowGram (fun _ : Fin r => (0 : EuclideanSpace ℝ (Fin p))) = 0 := by
    ext i j
    simp [meanRowGram, Matrix.sum_apply, Matrix.vecMulVec_apply]
  rw [hz]
  simp

end ResearchMain.WishartBlocks
