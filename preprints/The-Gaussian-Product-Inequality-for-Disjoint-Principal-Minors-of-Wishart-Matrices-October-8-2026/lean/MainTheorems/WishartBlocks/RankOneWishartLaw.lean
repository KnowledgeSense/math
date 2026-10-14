import MainTheorems.WishartBlocks.GaussianAffineLaplace
import Mathlib.MeasureTheory.Integral.Prod

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder InnerProductSpace

noncomputable def gaussianMeanGram {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (m z : EuclideanSpace ℝ (Fin p)) : Matrix (Fin p) (Fin p) ℝ :=
  let y := (CFC.sqrt S).toEuclideanLin z + m
  Matrix.vecMulVec (fun i => y i) (fun i => y i)

theorem trace_vectorGram {p : ℕ} (T : Matrix (Fin p) (Fin p) ℝ)
    (y : EuclideanSpace ℝ (Fin p)) :
    Matrix.trace (T * Matrix.vecMulVec (fun i => y i) (fun i => y i)) =
      ⟪y, T.toEuclideanLin y⟫_ℝ := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm,
    euclidean_dotProduct_matrix]

noncomputable def oneRowWishartValue {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (m : EuclideanSpace ℝ (Fin p))
    (wz : Matrix (Fin p) (Fin p) ℝ × EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ := wz.1 + gaussianMeanGram S m wz.2

noncomputable def oneRowWishartLaw {p : ℕ} (q : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (m : EuclideanSpace ℝ (Fin p)) : Measure (Matrix (Fin p) (Fin p) ℝ) :=
  ((bartlettLaw (q - 1) S).prod (stdGaussian (EuclideanSpace ℝ (Fin p)))).map
    (oneRowWishartValue S m)

theorem measurable_oneRowWishartValue {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (m : EuclideanSpace ℝ (Fin p)) : Measurable (oneRowWishartValue S m) := by
  have hy : Continuous (fun wz : Matrix (Fin p) (Fin p) ℝ × EuclideanSpace ℝ (Fin p) =>
      (CFC.sqrt S).toEuclideanLin wz.2 + m) :=
    ((CFC.sqrt S).toEuclideanLin.toContinuousLinearMap.continuous.comp continuous_snd).add
      continuous_const
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun wz : Matrix (Fin p) (Fin p) ℝ × EuclideanSpace ℝ (Fin p) =>
    wz.1 i j + ((CFC.sqrt S).toEuclideanLin wz.2 + m) i *
      ((CFC.sqrt S).toEuclideanLin wz.2 + m) j)
  have hW : Measurable (fun wz : Matrix (Fin p) (Fin p) ℝ × EuclideanSpace ℝ (Fin p) =>
      wz.1 i j) := by fun_prop
  exact hW.add (((PiLp.continuous_apply (p := 2) (fun _ : Fin p => ℝ) i).measurable.comp
    hy.measurable).mul ((PiLp.continuous_apply (p := 2) (fun _ : Fin p => ℝ) j).measurable.comp
      hy.measurable))

theorem measurable_gaussianMeanGram {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (m : EuclideanSpace ℝ (Fin p)) : Measurable (gaussianMeanGram S m) := by
  have h := (measurable_oneRowWishartValue S m).comp
    ((measurable_const : Measurable (fun _ : EuclideanSpace ℝ (Fin p) =>
      (0 : Matrix (Fin p) (Fin p) ℝ))).prodMk measurable_id)
  simpa only [Function.comp_def, oneRowWishartValue, zero_add, id_eq] using h

theorem measurable_gaussianMeanGram_joint {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ) :
    Measurable (fun mz : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p) =>
      gaussianMeanGram S mz.1 mz.2) := by
  have hy : Measurable (fun mz : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p) =>
      (CFC.sqrt S).toEuclideanLin mz.2 + mz.1) :=
    ((CFC.sqrt S).toEuclideanLin.toContinuousLinearMap.continuous.measurable.comp
      measurable_snd).add measurable_fst
  apply Measurable.of_eval_matrix
  intro i j
  exact ((PiLp.continuous_apply (p := 2) (fun _ : Fin p => ℝ) i).measurable.comp hy).mul
    ((PiLp.continuous_apply (p := 2) (fun _ : Fin p => ℝ) j).measurable.comp hy)

theorem oneRowWishart_probability {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (m : EuclideanSpace ℝ (Fin p)) :
    IsProbabilityMeasure (oneRowWishartLaw q S m) := by
  let : IsProbabilityMeasure (bartlettLaw (q - 1) S) :=
    bartlett_law_probability (by linarith) S
  unfold oneRowWishartLaw
  infer_instance

theorem oneRowWishart_positiveSemidefinite {p : ℕ} (q : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (m : EuclideanSpace ℝ (Fin p)) :
    ∀ᵐ W ∂(oneRowWishartLaw q S m), W.PosSemidef := by
  unfold oneRowWishartLaw
  rw [ae_map_iff (measurable_oneRowWishartValue S m).aemeasurable
    Matrix.posSemidef_is_closed.measurableSet]
  have hw : ∀ᵐ wz ∂((bartlettLaw (q - 1) S).prod
      (stdGaussian (EuclideanSpace ℝ (Fin p)))), wz.1.PosSemidef :=
    Measure.quasiMeasurePreserving_fst.ae (bartlettLaw_positiveSemidefinite (q - 1) S)
  filter_upwards [hw] with wz hwz
  apply hwz.add
  simpa only [gaussianMeanGram, star_trivial] using
    Matrix.posSemidef_vecMulVec_self_star
      (fun i => ((CFC.sqrt S).toEuclideanLin wz.2 + m) i)

theorem trace_gaussianMeanGram {p : ℕ} (T S : Matrix (Fin p) (Fin p) ℝ)
    (m z : EuclideanSpace ℝ (Fin p)) :
    Matrix.trace (T * gaussianMeanGram S m z) =
      ⟪(CFC.sqrt S).toEuclideanLin z + m,
        T.toEuclideanLin ((CFC.sqrt S).toEuclideanLin z + m)⟫_ℝ := by
  exact trace_vectorGram T _

theorem oneRowWishart_laplace {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    {S T : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hT : T.PosSemidef)
    (m : EuclideanSpace ℝ (Fin p)) :
    ∫ W, Real.exp (-Matrix.trace (T * W)) ∂(oneRowWishartLaw q S m) =
      (1 + (2 : ℝ) • (S * T)).det ^ (-q / 2) *
        Real.exp (-⟪m, (T * (1 + (2 : ℝ) • (S * T))⁻¹).toEuclideanLin m⟫_ℝ) := by
  let : IsProbabilityMeasure (bartlettLaw (q - 1) S) :=
    bartlett_law_probability (by linarith) S
  have hD := covariance_precision_det_pos hS.posSemidef hT
  unfold oneRowWishartLaw
  rw [integral_map (measurable_oneRowWishartValue S m).aemeasurable
    (continuous_exp_trace_mul T).measurable.aestronglyMeasurable]
  simp_rw [oneRowWishartValue, Matrix.mul_add, Matrix.trace_add, neg_add, Real.exp_add,
    trace_gaussianMeanGram]
  rw [integral_prod_mul (fun W : Matrix (Fin p) (Fin p) ℝ => Real.exp (-Matrix.trace (T * W)))
    (fun z : EuclideanSpace ℝ (Fin p) =>
      Real.exp (-⟪(CFC.sqrt S).toEuclideanLin z + m,
        T.toEuclideanLin ((CFC.sqrt S).toEuclideanLin z + m)⟫_ℝ)),
    bartlettLaw_laplace (by linarith) hS.posSemidef hT,
    gaussian_affine_laplace hS hT, Real.sqrt_eq_rpow,
    ← Real.rpow_neg hD.le]
  rw [← mul_assoc, ← Real.rpow_add hD]
  congr 1
  congr 1
  ring

theorem oneRowWishart_rankOne_laplace {p : ℕ} {q θ : ℝ} (hq : (p : ℝ) < q)
    (hθ : 0 ≤ θ) {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosSemidef) (v : EuclideanSpace ℝ (Fin p)) :
    ∫ W, Real.exp (-Matrix.trace (T * W))
        ∂(oneRowWishartLaw q S (Real.sqrt θ • v)) =
      (1 + (2 : ℝ) • (S * T)).det ^ (-q / 2) *
        Real.exp (-θ * ⟪v, (T * (1 + (2 : ℝ) • (S * T))⁻¹).toEuclideanLin v⟫_ℝ) := by
  rw [oneRowWishart_laplace hq hS hT]
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  rw [← mul_assoc, Real.mul_self_sqrt hθ, neg_mul]

theorem oneRowWishart_zero_mean {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) :
    oneRowWishartLaw q S 0 = bartlettLaw q S := by
  let : IsProbabilityMeasure (oneRowWishartLaw q S 0) := oneRowWishart_probability hq S 0
  let : IsProbabilityMeasure (bartlettLaw q S) := bartlett_law_probability (by linarith) S
  apply matrix_measure_eq_of_positive_laplace
    (oneRowWishart_positiveSemidefinite q S 0) (bartlettLaw_positiveSemidefinite q S)
  intro T hT
  rw [oneRowWishart_laplace hq hS hT,
    bartlettLaw_laplace (by linarith) hS.posSemidef hT]
  simp

end ResearchMain.WishartBlocks
