import MainTheorems.WishartBlocks.BartlettLaplace

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder

theorem continuous_exp_trace_mul {p : ℕ} (T : Matrix (Fin p) (Fin p) ℝ) :
    Continuous (fun W : Matrix (Fin p) (Fin p) ℝ => Real.exp (-Matrix.trace (T * W))) := by
  unfold Matrix.trace
  fun_prop

theorem trace_gram_congruence {p : ℕ} (T R B : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (T * ((R * B) * (R * B).transpose)) =
      Matrix.trace ((R.transpose * T * R) * (B * B.transpose)) := by
  calc
    _ = Matrix.trace ((T * R) * ((B * B.transpose) * R.transpose)) := by
      congr 1
      rw [Matrix.transpose_mul]
      noncomm_ring
    _ = Matrix.trace (R.transpose * ((T * R) * (B * B.transpose))) :=
      Matrix.trace_mul_cycle' _ _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem sqrt_congruence_precision_det {p : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef)
    (T : Matrix (Fin p) (Fin p) ℝ) :
    (1 + (2 : ℝ) • ((CFC.sqrt S).transpose * T * CFC.sqrt S)).det =
      (1 + (2 : ℝ) • (S * T)).det := by
  have hR : (CFC.sqrt S).PosSemidef := (CFC.sqrt_nonneg S).posSemidef
  have hRt : (CFC.sqrt S).transpose = CFC.sqrt S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.1.eq
  have hSq : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  calc
    _ = (1 + (((2 : ℝ) • CFC.sqrt S) * T) * CFC.sqrt S).det := by
      rw [hRt, Matrix.smul_mul, Matrix.smul_mul]
    _ = (1 + CFC.sqrt S * (((2 : ℝ) • CFC.sqrt S) * T)).det :=
      Matrix.det_one_add_mul_comm _ _
    _ = _ := by rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, hSq]

theorem bartlettLaw_laplace {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) :
    ∫ W, Real.exp (-Matrix.trace (T * W)) ∂(bartlettLaw α S) =
      (1 + (2 : ℝ) • (S * T)).det ^ (-α / 2) := by
  have hTest : ((CFC.sqrt S).transpose * T * CFC.sqrt S).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hT.conjTranspose_mul_mul_same (CFC.sqrt S)
  have hf := continuous_exp_trace_mul T
  unfold bartlettLaw
  rw [integral_map (measurable_bartlettValue S).aemeasurable hf.measurable.aestronglyMeasurable]
  simp_rw [bartlettValue, trace_gram_congruence]
  rw [bartlett_gram_laplace hα hTest, sqrt_congruence_precision_det hS]

theorem covariance_precision_det_pos {p : ℕ} {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) :
    0 < (1 + (2 : ℝ) • (S * T)).det := by
  rw [← sqrt_congruence_precision_det hS T]
  have hA : ((CFC.sqrt S).transpose * T * CFC.sqrt S).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hT.conjTranspose_mul_mul_same (CFC.sqrt S)
  rw [matrix_one_add_smul_det hA.1]
  apply Finset.prod_pos
  intro i _
  have hEig := hA.eigenvalues_nonneg i
  positivity

end ResearchMain.WishartBlocks
