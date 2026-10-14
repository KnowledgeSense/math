import MainTheorems.WishartBlocks.PositiveMatrixLaplaceUniqueness

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder

def matrixCongruence {p m : ℕ} (C : Matrix (Fin m) (Fin p) ℝ)
    (W : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin m) (Fin m) ℝ := C * W * C.transpose

theorem measurable_matrixCongruence {p m : ℕ} (C : Matrix (Fin m) (Fin p) ℝ) :
    Measurable (matrixCongruence C) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [matrixCongruence, Matrix.mul_apply]
  fun_prop

theorem trace_matrixCongruence {p m : ℕ} (C : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin m) ℝ) (W : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (T * matrixCongruence C W) =
      Matrix.trace ((C.transpose * T * C) * W) := by
  calc
    _ = Matrix.trace ((T * C) * (W * C.transpose)) := by
      congr 1
      simp only [matrixCongruence, Matrix.mul_assoc]
    _ = Matrix.trace (C.transpose * ((T * C) * W)) := Matrix.trace_mul_cycle' _ _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem congruence_precision_det {p m : ℕ} (C : Matrix (Fin m) (Fin p) ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin m) (Fin m) ℝ) :
    (1 + (2 : ℝ) • (S * (C.transpose * T * C))).det =
      (1 + (2 : ℝ) • (matrixCongruence C S * T)).det := by
  calc
    _ = (1 + (((2 : ℝ) • S) * C.transpose * T) * C).det := by
      simp only [Matrix.smul_mul, Matrix.mul_assoc]
    _ = (1 + C * (((2 : ℝ) • S) * C.transpose * T)).det :=
      Matrix.det_one_add_mul_comm _ _
    _ = _ := by simp only [matrixCongruence, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc]

theorem bartlettLaw_covariance_congruence {p m : ℕ} {α : ℝ}
    (hαp : (p : ℝ) - 1 < α) (hαm : (m : ℝ) - 1 < α)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef)
    (C : Matrix (Fin m) (Fin p) ℝ) :
    (bartlettLaw α S).map (matrixCongruence C) =
      bartlettLaw α (matrixCongruence C S) := by
  let : IsProbabilityMeasure (bartlettLaw α S) := bartlett_law_probability hαp S
  let : IsProbabilityMeasure (bartlettLaw α (matrixCongruence C S)) :=
    bartlett_law_probability hαm _
  have hCov : (matrixCongruence C S).PosSemidef := by
    simpa only [matrixCongruence, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS.mul_mul_conjTranspose_same C
  apply matrix_measure_eq_of_positive_laplace
  · rw [ae_map_iff (measurable_matrixCongruence C).aemeasurable
      Matrix.posSemidef_is_closed.measurableSet]
    filter_upwards [bartlettLaw_positiveSemidefinite α S] with W hW
    simpa only [matrixCongruence, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hW.mul_mul_conjTranspose_same C
  · exact bartlettLaw_positiveSemidefinite α _
  · intro T hT
    have hTest : (C.transpose * T * C).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hT.conjTranspose_mul_mul_same C
    rw [integral_map (measurable_matrixCongruence C).aemeasurable
      (continuous_exp_trace_mul T).measurable.aestronglyMeasurable]
    simp_rw [trace_matrixCongruence]
    rw [bartlettLaw_laplace hαp hS hTest, bartlettLaw_laplace hαm hCov hT,
      congruence_precision_det]

end ResearchMain.WishartBlocks
