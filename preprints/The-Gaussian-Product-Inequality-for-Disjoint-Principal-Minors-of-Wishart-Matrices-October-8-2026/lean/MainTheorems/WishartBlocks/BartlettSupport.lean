import MainTheorems.WishartBlocks.BartlettLaw
import MainTheorems.WishartBlocks.GammaMoments
import Mathlib.LinearAlgebra.Matrix.Block

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped BigOperators MatrixOrder

theorem bartlettMatrix_lowerTriangular {p : ℕ} (x : Fin p × Fin p → ℝ) :
    (bartlettMatrix x).IsLowerTriangular := by
  intro i j hij
  have h : i < j := hij
  simp [bartlettMatrix, h.ne, not_lt_of_ge h.le]

theorem bartlettMatrix_determinant {p : ℕ} (x : Fin p × Fin p → ℝ) :
    (bartlettMatrix x).det = ∏ i, Real.sqrt (x (i, i)) := by
  rw [Matrix.det_of_isLowerTriangular _ (bartlettMatrix_lowerTriangular x)]
  simp [bartlettMatrix]

theorem bartlettMatrix_determinant_pos {p : ℕ} {x : Fin p × Fin p → ℝ}
    (hx : ∀ i, 0 < x (i, i)) : 0 < (bartlettMatrix x).det := by
  rw [bartlettMatrix_determinant]
  exact Finset.prod_pos fun i _ => Real.sqrt_pos.mpr (hx i)

theorem bartlett_diagonal_ae_positive {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    ∀ᵐ x ∂(bartlettMeasure p α), ∀ i, 0 < x (i, i) := by
  let : ∀ ij : Fin p × Fin p, IsProbabilityMeasure (bartlettCoordinate α ij) :=
    bartlett_coordinate_probability hα
  apply Filter.eventually_all.mpr
  intro i
  have hi : ∀ᵐ t ∂(bartlettCoordinate α (i, i)), 0 < t := by
    simpa [bartlettCoordinate] using
      gammaMeasure_ae_positive ((α - (i : ℕ)) / 2) (1 / 2)
  exact (Measure.tendsto_eval_ae_ae (μ := bartlettCoordinate α) (i := (i, i))).eventually hi

theorem bartlettValue_positiveDefinite {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) {x : Fin p × Fin p → ℝ} (hx : ∀ i, 0 < x (i, i)) :
    (bartlettValue S x).PosDef := by
  apply (bartlettValue_positiveSemidefinite S x).posDef_iff_det_ne_zero.mpr
  unfold bartlettValue
  simp only [Matrix.det_mul, Matrix.det_transpose]
  have hs : (CFC.sqrt S).det ≠ 0 := by
    rw [hS.posSemidef.det_sqrt, RCLike.sqrt_real]
    exact (Real.sqrt_pos.mpr hS.det_pos).ne'
  have hb := (bartlettMatrix_determinant_pos hx).ne'
  exact mul_ne_zero (mul_ne_zero hs hb) (mul_ne_zero hs hb)

theorem measurableSet_positiveDefinite (p : ℕ) :
    MeasurableSet {W : Matrix (Fin p) (Fin p) ℝ | W.PosDef} := by
  have he : {W : Matrix (Fin p) (Fin p) ℝ | W.PosDef} =
      {W | W.PosSemidef} ∩ {W | W.det ≠ 0} := by
    ext W
    constructor
    · intro h
      exact ⟨h.posSemidef, h.det_pos.ne'⟩
    · rintro ⟨h, hd⟩
      exact h.posDef_iff_det_ne_zero.mpr hd
  rw [he]
  apply Matrix.posSemidef_is_closed.measurableSet.inter
  exact (isClosed_eq (by fun_prop : Continuous (fun W : Matrix (Fin p) (Fin p) ℝ => W.det))
    continuous_const).measurableSet.compl

theorem bartlettLaw_positiveDefinite {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) :
    ∀ᵐ W ∂(bartlettLaw α S), W.PosDef := by
  unfold bartlettLaw
  rw [ae_map_iff (measurable_bartlettValue S).aemeasurable (measurableSet_positiveDefinite p)]
  filter_upwards [bartlett_diagonal_ae_positive hα] with x hx
  exact bartlettValue_positiveDefinite hS hx

end ResearchMain.WishartBlocks
