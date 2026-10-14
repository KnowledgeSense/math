import MainTheorems.WishartBlocks.NoncentralWishartLaw
import MainTheorems.WishartBlocks.ResolventPositivity

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder InnerProductSpace

theorem matrix_rows_gram {k m : ℕ} (R : Matrix (Fin k) (Fin m) ℝ) :
    meanRowGram (fun i => WithLp.toLp 2 (R i)) = R.transpose * R := by
  ext i j
  simp only [meanRowGram, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Matrix.mul_apply, Matrix.transpose_apply]

noncomputable def regressionMean {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (K : Matrix (Fin k) (Fin m) ℝ) (x : Fin k × Fin k → ℝ) :
    Fin k → EuclideanSpace ℝ (Fin m) :=
  fun i => WithLp.toLp 2 (((CFC.sqrt A * bartlettMatrix x).transpose * K) i)

theorem measurable_regressionMean {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (K : Matrix (Fin k) (Fin m) ℝ) : Measurable (regressionMean A K) := by
  unfold regressionMean
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp 2 (Fin m → ℝ)).comp
  apply Measurable.of_eval
  intro j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.measurable_sum
  intro l _
  apply Measurable.mul_const
  apply Finset.measurable_sum
  intro t _
  exact measurable_const.mul
    ((measurable_bartlettMatrix (p := k)).eval_matrix (i := t) (j := i))

theorem regressionMean_gram {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (K : Matrix (Fin k) (Fin m) ℝ) (x : Fin k × Fin k → ℝ) :
    meanRowGram (regressionMean A K x) = K.transpose * bartlettValue A x * K := by
  unfold regressionMean
  rw [matrix_rows_gram, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  simp only [bartlettValue, Matrix.mul_assoc]

theorem regressionMean_trace {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (K : Matrix (Fin k) (Fin m) ℝ) (x : Fin k × Fin k → ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.trace (meanRowGram (regressionMean A K x) * R) =
      Matrix.trace ((K * R * K.transpose) * bartlettValue A x) := by
  rw [regressionMean_gram]
  calc
    _ = Matrix.trace ((K.transpose * bartlettValue A x) * (K * R)) := by
      rw [Matrix.mul_assoc]
    _ = Matrix.trace ((K * R) * (K.transpose * bartlettValue A x)) :=
      Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

noncomputable def regressionInputLaw {k m : ℕ} (α : ℝ)
    (S : Matrix (Fin m) (Fin m) ℝ) :
    Measure ((Fin k × Fin k → ℝ) ×
      (Matrix (Fin m) (Fin m) ℝ × (Fin k → EuclideanSpace ℝ (Fin m)))) :=
  (bartlettMeasure k α).prod ((bartlettLaw (α - (k : ℝ)) S).prod
    (Measure.pi fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin m))))

noncomputable def regressionPairValue {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (S : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin k) (Fin m) ℝ)
    (xvz : (Fin k × Fin k → ℝ) ×
      (Matrix (Fin m) (Fin m) ℝ × (Fin k → EuclideanSpace ℝ (Fin m)))) :
    Matrix (Fin k) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ :=
  (bartlettValue A xvz.1, noncentralWishartValue S (regressionMean A K xvz.1) xvz.2)

theorem regressionInput_probability {k m : ℕ} {α : ℝ}
    (hα : ((k + m : ℕ) : ℝ) - 1 < α) (S : Matrix (Fin m) (Fin m) ℝ) :
    IsProbabilityMeasure (regressionInputLaw (k := k) α S) := by
  have hαk : (k : ℝ) - 1 < α := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hα
    linarith
  have hαm : (m : ℝ) - 1 < α - (k : ℝ) := by
    push_cast at hα
    linarith
  let : IsProbabilityMeasure (bartlettMeasure k α) := bartlett_measure_probability hαk
  let : IsProbabilityMeasure (bartlettLaw (α - (k : ℝ)) S) := bartlett_law_probability hαm S
  unfold regressionInputLaw
  infer_instance

theorem regressionPair_measurable {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (S : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin k) (Fin m) ℝ) :
    Measurable (regressionPairValue A S K) := by
  let : MeasurableAdd₂ (Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (MeasurableAdd₂ (Fin m → Fin m → ℝ))
  have hm : Measurable (fun xvz : (Fin k × Fin k → ℝ) ×
      (Matrix (Fin m) (Fin m) ℝ × (Fin k → EuclideanSpace ℝ (Fin m))) =>
      regressionMean A K xvz.1) := (measurable_regressionMean A K).comp measurable_fst
  have hv : Measurable (fun xvz : (Fin k × Fin k → ℝ) ×
      (Matrix (Fin m) (Fin m) ℝ × (Fin k → EuclideanSpace ℝ (Fin m))) =>
      xvz.2.1) := measurable_fst.comp measurable_snd
  have hz : Measurable (fun xvz : (Fin k × Fin k → ℝ) ×
      (Matrix (Fin m) (Fin m) ℝ × (Fin k → EuclideanSpace ℝ (Fin m))) =>
      xvz.2.2) := measurable_snd.comp measurable_snd
  have hg (i : Fin k) : Measurable (fun xvz : (Fin k × Fin k → ℝ) ×
      (Matrix (Fin m) (Fin m) ℝ × (Fin k → EuclideanSpace ℝ (Fin m))) =>
      gaussianMeanGram S (regressionMean A K xvz.1 i) (xvz.2.2 i)) := by
    simpa only [Function.comp_def] using (measurable_gaussianMeanGram_joint S).comp
      (((measurable_pi_apply i).comp hm).prodMk ((measurable_pi_apply i).comp hz))
  unfold regressionPairValue noncentralWishartValue
  apply Measurable.prodMk
  · exact (measurable_bartlettValue A).comp measurable_fst
  · exact hv.add (Finset.measurable_fun_sum Finset.univ (fun i _ => hg i))

theorem regressionPair_positiveSemidefinite {k m : ℕ} {α : ℝ}
    (hα : ((k + m : ℕ) : ℝ) - 1 < α)
    (A : Matrix (Fin k) (Fin k) ℝ) (S : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin k) (Fin m) ℝ) :
    ∀ᵐ xvz ∂(regressionInputLaw (k := k) α S),
      (regressionPairValue A S K xvz).1.PosSemidef ∧
        (regressionPairValue A S K xvz).2.PosSemidef := by
  have hαm : (m : ℝ) - 1 < α - (k : ℝ) := by push_cast at hα; linarith
  let : IsProbabilityMeasure (bartlettLaw (α - (k : ℝ)) S) := bartlett_law_probability hαm S
  have hv : ∀ᵐ vz ∂((bartlettLaw (α - (k : ℝ)) S).prod
      (Measure.pi fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin m)))),
      vz.1.PosSemidef := Measure.quasiMeasurePreserving_fst.ae
    (bartlettLaw_positiveSemidefinite (α - (k : ℝ)) S)
  have hv' : ∀ᵐ xvz ∂(regressionInputLaw (k := k) α S), xvz.2.1.PosSemidef :=
    Measure.quasiMeasurePreserving_snd.ae hv
  filter_upwards [hv'] with xvz hxvz
  refine ⟨bartlettValue_positiveSemidefinite A _, hxvz.add ?_⟩
  apply Matrix.posSemidef_sum
  intro i _
  simpa only [gaussianMeanGram, star_trivial] using
    Matrix.posSemidef_vecMulVec_self_star
      (fun j => ((CFC.sqrt S).toEuclideanLin (xvz.2.2 i) + regressionMean A K xvz.1 i) j)

theorem regressionPair_laplace {k m : ℕ} {α : ℝ}
    (hα : ((k + m : ℕ) : ℝ) - 1 < α)
    {A : Matrix (Fin k) (Fin k) ℝ} {S : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (hS : S.PosDef) (K : Matrix (Fin k) (Fin m) ℝ)
    {T : Matrix (Fin k) (Fin k) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    (hT : T.PosSemidef) (hU : U.PosSemidef) :
    ∫ xvz, Real.exp (-(Matrix.trace (T * (regressionPairValue A S K xvz).1) +
        Matrix.trace (U * (regressionPairValue A S K xvz).2)))
        ∂(regressionInputLaw (k := k) α S) =
      (1 + (2 : ℝ) • (S * U)).det ^ (-α / 2) *
        (1 + (2 : ℝ) • (A *
          (T + K * (U * (1 + (2 : ℝ) • (S * U))⁻¹) * K.transpose))).det ^ (-α / 2) := by
  have hαk : (k : ℝ) - 1 < α := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hα
    linarith
  have hαm : (m : ℝ) - 1 < α - (k : ℝ) := by push_cast at hα; linarith
  let : IsProbabilityMeasure (regressionInputLaw (k := k) α S) :=
    regressionInput_probability hα S
  let : IsProbabilityMeasure (bartlettMeasure k α) := bartlett_measure_probability hαk
  let : IsProbabilityMeasure (bartlettLaw (α - (k : ℝ)) S) := bartlett_law_probability hαm S
  let C := K * (U * (1 + (2 : ℝ) • (S * U))⁻¹) * K.transpose
  have hC : C.PosSemidef := by
    simpa only [C, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (covariance_resolvent_positiveSemidefinite hS hU).mul_mul_conjTranspose_same K
  have hF := hT.add hC
  let f := fun xvz => Real.exp (-(Matrix.trace (T * (regressionPairValue A S K xvz).1) +
    Matrix.trace (U * (regressionPairValue A S K xvz).2)))
  have hmPair := regressionPair_measurable A S K
  have hmT := (continuous_exp_trace_mul T).measurable.comp (measurable_fst.comp hmPair)
  have hmU := (continuous_exp_trace_mul U).measurable.comp (measurable_snd.comp hmPair)
  have hmf : Measurable f := by
    simpa only [f, neg_add, Real.exp_add, Function.comp_def] using hmT.fun_mul hmU
  have hf : Integrable f (regressionInputLaw (k := k) α S) := by
    apply (integrable_const (1 : ℝ)).mono' hmf.aestronglyMeasurable
    filter_upwards [regressionPair_positiveSemidefinite hα A S K] with xvz hxvz
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (add_nonneg (trace_positive_product hT hxvz.1)
      (trace_positive_product hU hxvz.2))
  change ∫ xvz, f xvz ∂(regressionInputLaw (k := k) α S) = _
  rw [regressionInputLaw, integral_prod _ hf]
  have hi (x : Fin k × Fin k → ℝ) :
      ∫ vz, Real.exp (-Matrix.trace (U * noncentralWishartValue S (regressionMean A K x) vz))
        ∂((bartlettLaw (α - (k : ℝ)) S).prod
          (Measure.pi fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin m)))) =
        (1 + (2 : ℝ) • (S * U)).det ^ (-α / 2) *
          Real.exp (-Matrix.trace (C * bartlettValue A x)) := by
    have hh := noncentralWishart_laplace hαm hS hU (regressionMean A K x)
    rw [noncentralWishartLaw, integral_map
      (measurable_noncentralWishartValue S _).aemeasurable
        (continuous_exp_trace_mul U).measurable.aestronglyMeasurable,
      regressionMean_trace] at hh
    exact hh
  simp only [f, regressionPairValue, neg_add, Real.exp_add]
  simp_rw [integral_const_mul, hi]
  have he (x : Fin k × Fin k → ℝ) :
      Real.exp (-Matrix.trace (T * bartlettValue A x)) *
          ((1 + (2 : ℝ) • (S * U)).det ^ (-α / 2) *
            Real.exp (-Matrix.trace (C * bartlettValue A x))) =
        (1 + (2 : ℝ) • (S * U)).det ^ (-α / 2) *
          Real.exp (-Matrix.trace ((T + C) * bartlettValue A x)) := by
    rw [Matrix.add_mul, Matrix.trace_add, neg_add, Real.exp_add]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  have hh := bartlettLaw_laplace hαk hA hF
  rw [bartlettLaw, integral_map (measurable_bartlettValue A).aemeasurable
    (continuous_exp_trace_mul (T + C)).measurable.aestronglyMeasurable] at hh
  exact hh

end ResearchMain.WishartBlocks
