import MainTheorems.WishartBlocks.RegularizedMatrices
import MainTheorems.WishartBlocks.RankTwoDirections
import MainTheorems.WishartBlocks.LaplaceStripContinuation

namespace ResearchMain.WishartBlocks

open MeasureTheory Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

noncomputable def matrixStripRadius {p : ℕ} (U : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  1 / (1 + (p : ℝ) ^ 2 * ‖U‖)

theorem matrixStripRadius_pos {p : ℕ} (U : Matrix (Fin p) (Fin p) ℝ) :
    0 < matrixStripRadius U := by unfold matrixStripRadius; positivity

theorem matrixStripRadius_mul_bound {p : ℕ} (U : Matrix (Fin p) (Fin p) ℝ) :
    matrixStripRadius U * ((p : ℝ) ^ 2 * ‖U‖) < 1 := by
  unfold matrixStripRadius
  rw [one_div_mul_eq_div]
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem hermitian_positive_of_trace_nonneg {p : ℕ}
    {A : Matrix (Fin p) (Fin p) ℝ} (hA : A.IsHermitian)
    (h : ∀ W : Matrix (Fin p) (Fin p) ℝ, W.PosSemidef → 0 ≤ (A * W).trace) :
    A.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA
  intro x
  have hx : (Matrix.vecMulVec x x).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star x
  simpa only [trace_matrix_outer, star_trivial] using h _ hx

theorem trace_direction_bound_on_positive {p : ℕ} (U : Matrix (Fin p) (Fin p) ℝ)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) :
    |(U * W).trace| ≤ ((p : ℝ) ^ 2 * ‖U‖) * W.trace := by
  simpa only [Real.norm_eq_abs] using trace_product_entry_bound U W (norm_nonneg U)
    (fun _ _ => Matrix.norm_entry_le_entrywise_sup_norm U)
    (positiveSemidefinite_entry_le_trace hW)

theorem matrixStripRadius_trace_damping {p : ℕ} (U : Matrix (Fin p) (Fin p) ℝ)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) :
    matrixStripRadius U * |(U * W).trace| ≤ W.trace := by
  calc
    _ ≤ matrixStripRadius U * (((p : ℝ) ^ 2 * ‖U‖) * W.trace) :=
      mul_le_mul_of_nonneg_left (trace_direction_bound_on_positive U hW)
        (matrixStripRadius_pos U).le
    _ = (matrixStripRadius U * ((p : ℝ) ^ 2 * ‖U‖)) * W.trace := by ring
    _ ≤ 1 * W.trace := mul_le_mul_of_nonneg_right
      (matrixStripRadius_mul_bound U).le hW.trace_nonneg
    _ = _ := one_mul _

theorem identity_shift_trace {p : ℕ} (U W : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
    ((1 + t • U) * W).trace = W.trace + t * (U * W).trace := by
  simp only [Matrix.add_mul, one_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul]

theorem identity_shift_positive {p : ℕ} {U : Matrix (Fin p) (Fin p) ℝ}
    (hU : U.IsHermitian) {t : ℝ} (ht : |t| < matrixStripRadius U) :
    (1 + t • U).PosSemidef := by
  have hH : (1 + t • U).IsHermitian := by
    change (1 + t • U).conjTranspose = 1 + t • U
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, star_trivial, hU.eq]
  apply hermitian_positive_of_trace_nonneg hH
  intro W hW
  rw [identity_shift_trace]
  have habs : |t * (U * W).trace| ≤ W.trace := by
    rw [abs_mul]
    calc
      _ ≤ matrixStripRadius U * |(U * W).trace| :=
        mul_le_mul_of_nonneg_right ht.le (abs_nonneg _)
      _ ≤ W.trace := matrixStripRadius_trace_damping U hW
  linarith [neg_le_abs (t * (U * W).trace)]

theorem matrix_weightedLaplace_real {p : ℕ} (μ : Measure (Matrix (Fin p) (Fin p) ℝ))
    (U : Matrix (Fin p) (Fin p) ℝ) (c : Matrix (Fin p) (Fin p) ℝ → ℂ) (t : ℝ) :
    weightedLaplace μ Matrix.trace (fun W => (U * W).trace) c t =
      ∫ W, c W * (Real.exp (-((1 + t • U) * W).trace) : ℂ) ∂μ := by
  unfold weightedLaplace
  apply integral_congr_ae
  exact ae_of_all _ fun W => by
    change c W * Complex.exp (-(W.trace : ℂ) - (t : ℂ) * ((U * W).trace : ℂ)) =
      c W * (Real.exp (-((1 + t • U) * W).trace) : ℂ)
    have he : -(W.trace : ℂ) - (t : ℂ) * ((U * W).trace : ℂ) =
        (-((1 + t • U) * W).trace : ℝ) := by
      rw [identity_shift_trace]
      push_cast
      ring
    rw [he, ← Complex.ofReal_exp]

theorem matrix_polynomial_laplace_imaginary_zero {p : ℕ} {ι : Type*} [Fintype ι]
    (μ : Measure (Matrix (Fin p) (Fin p) ℝ))
    (hμ : ∀ᵐ W ∂μ, W.PosSemidef) {U : Matrix (Fin p) (Fin p) ℝ}
    (hU : U.IsHermitian) (c : ι → Matrix (Fin p) (Fin p) ℝ → ℂ)
    (P : ι → Polynomial ℂ) (hc : ∀ i, Measurable (c i))
    (hi : ∀ i, Integrable (c i) μ)
    (hbi : ∀ i, Integrable (fun W => |(U * W).trace| * ‖c i W‖) μ)
    (hreal : ∀ t : ℝ, (1 + t • U).PosSemidef →
      (∑ i, (P i).eval (t : ℂ) *
        ∫ W, c i W * (Real.exp (-((1 + t • U) * W).trace) : ℂ) ∂μ) = 0)
    (y : ℝ) :
    (∑ i, (P i).eval (Complex.I * y) *
      weightedLaplace μ Matrix.trace (fun W => (U * W).trace) (c i) (Complex.I * y)) = 0 := by
  apply polynomial_weightedLaplace_imaginary_zero (by fun_prop) (by fun_prop)
    c P hc hi hbi (matrixStripRadius_pos U)
  · filter_upwards [hμ] with W hW
    exact matrixStripRadius_trace_damping U hW
  · intro t ht
    simp_rw [matrix_weightedLaplace_real]
    exact hreal t (identity_shift_positive hU ht)

end ResearchMain.WishartBlocks
