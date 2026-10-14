import MainTheorems.WishartBlocks.MatrixBlockUtilities

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder

noncomputable def regressionFiniteCovariance {k m : ℕ}
    (A : Matrix (Fin k) (Fin k) ℝ) (S : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin k) (Fin m) ℝ) : Matrix (Fin (k + m)) (Fin (k + m)) ℝ :=
  (regressionCovariance A S K).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem wishart_block_regression {k m : ℕ} {α : ℝ}
    (hα : ((k + m : ℕ) : ℝ) - 1 < α)
    {A : Matrix (Fin k) (Fin k) ℝ} {S : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (hS : S.PosDef) (K : Matrix (Fin k) (Fin m) ℝ) :
    (regressionInputLaw (k := k) α S).map (regressionPairValue A S K) =
      (bartlettLaw α (regressionFiniteCovariance A S K)).map
        (principalPair (k := k) (m := m)) := by
  let : MeasurableSpace.CountablySeparated
      (Matrix (Fin (k + m)) (Fin (k + m)) ℝ) :=
    inferInstanceAs (MeasurableSpace.CountablySeparated (Fin (k + m) → Fin (k + m) → ℝ))
  let : StandardBorelSpace (Matrix (Fin k) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (StandardBorelSpace ((Fin k → Fin k → ℝ) × (Fin m → Fin m → ℝ)))
  let : IsProbabilityMeasure (regressionInputLaw (k := k) α S) :=
    regressionInput_probability hα S
  let : IsProbabilityMeasure (bartlettLaw α (regressionFiniteCovariance A S K)) :=
    bartlett_law_probability hα _
  have hCov : (regressionFiniteCovariance A S K).PosSemidef :=
    (regressionCovariance_positiveSemidefinite hA hS.posSemidef K).submatrix
      finSumFinEquiv.symm
  apply (measurable_diagonalPairMatrix.measurableEmbedding
    diagonalPairMatrix_injective).map_injective
  rw [Measure.map_map measurable_diagonalPairMatrix (regressionPair_measurable A S K),
    Measure.map_map measurable_diagonalPairMatrix measurable_principalPair]
  let f := diagonalPairMatrix ∘ regressionPairValue A S K
  let g := diagonalPairMatrix ∘ (principalPair (k := k) (m := m))
  have hf : Measurable f := measurable_diagonalPairMatrix.comp
    (regressionPair_measurable A S K)
  have hg : Measurable g := measurable_diagonalPairMatrix.comp measurable_principalPair
  apply matrix_measure_eq_of_positive_laplace
  · rw [ae_map_iff hf.aemeasurable Matrix.posSemidef_is_closed.measurableSet]
    filter_upwards [regressionPair_positiveSemidefinite hα A S K] with xvz hxvz
    exact diagonalPairMatrix_positiveSemidefinite hxvz.1 hxvz.2
  · rw [ae_map_iff hg.aemeasurable Matrix.posSemidef_is_closed.measurableSet]
    filter_upwards [bartlettLaw_positiveSemidefinite α
      (regressionFiniteCovariance A S K)] with W hW
    have hPair := principalPair_positiveSemidefinite (k := k) (m := m) hW
    exact diagonalPairMatrix_positiveSemidefinite hPair.1 hPair.2
  · intro T hT
    let TA := (principalPair (k := k) (m := m) T).1
    let TB := (principalPair (k := k) (m := m) T).2
    have hPair := principalPair_positiveSemidefinite (k := k) (m := m) hT
    have hTA : TA.PosSemidef := hPair.1
    have hTB : TB.PosSemidef := hPair.2
    let D := diagonalPairMatrix (TA, TB)
    have hD : D.PosSemidef := diagonalPairMatrix_positiveSemidefinite hTA hTB
    rw [integral_map hf.aemeasurable
      (continuous_exp_trace_mul T).measurable.aestronglyMeasurable,
      integral_map hg.aemeasurable
        (continuous_exp_trace_mul T).measurable.aestronglyMeasurable]
    change (∫ xvz, Real.exp (-Matrix.trace (T * f xvz))
      ∂(regressionInputLaw (k := k) α S)) =
        ∫ W, Real.exp (-Matrix.trace (T * g W))
          ∂(bartlettLaw α (regressionFiniteCovariance A S K))
    simp_rw [f, g, Function.comp_apply, trace_diagonal_projection,
      trace_diagonalPairMatrix]
    rw [regressionPair_laplace hα hA hS K hTA hTB]
    have hLT := bartlettLaw_laplace hα hCov hD
    change (∫ W, Real.exp (-Matrix.trace (D * W))
      ∂(bartlettLaw α (regressionFiniteCovariance A S K))) = _ at hLT
    have hdet :
        (1 + (2 : ℝ) • (regressionFiniteCovariance A S K * D)).det =
          (1 + (2 : ℝ) • (S * TB)).det *
            (1 + (2 : ℝ) • (A *
              (TA + K * (TB * (1 + (2 : ℝ) • (S * TB))⁻¹) * K.transpose))).det := by
      dsimp only [regressionFiniteCovariance, D, diagonalPairMatrix]
      rw [precision_reindex_det, regression_precision_det A TA hS.posSemidef hTB K]
    have hR := covariance_resolvent_positiveSemidefinite hS hTB
    have hC : (K * (TB * (1 + (2 : ℝ) • (S * TB))⁻¹) * K.transpose).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hR.mul_mul_conjTranspose_same K
    have h1 := covariance_precision_det_pos hS.posSemidef hTB
    have h2 := covariance_precision_det_pos hA (hTA.add hC)
    rw [hLT, hdet, Real.mul_rpow h1.le h2.le]

end ResearchMain.WishartBlocks
