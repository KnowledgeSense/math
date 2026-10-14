import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

noncomputable def bartlettCoordinate {p : ℕ} (α : ℝ) (ij : Fin p × Fin p) : Measure ℝ :=
  if ij.1 = ij.2 then gammaMeasure ((α - (ij.1 : ℕ)) / 2) (1 / 2)
  else gaussianReal 0 1

noncomputable def bartlettMeasure (p : ℕ) (α : ℝ) : Measure (Fin p × Fin p → ℝ) :=
  Measure.pi (bartlettCoordinate α)

noncomputable def bartlettMatrix {p : ℕ} (x : Fin p × Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j => if i = j then Real.sqrt (x (i, j)) else if j < i then x (i, j) else 0

noncomputable def bartlettValue {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (x : Fin p × Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  let Q := CFC.sqrt S * bartlettMatrix x
  Q * Q.transpose

noncomputable def bartlettLaw {p : ℕ} (α : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measure (Matrix (Fin p) (Fin p) ℝ) :=
  (bartlettMeasure p α).map (bartlettValue S)

theorem bartlett_coordinate_probability {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α)
    (ij : Fin p × Fin p) : IsProbabilityMeasure (bartlettCoordinate α ij) := by
  unfold bartlettCoordinate
  split_ifs
  · apply isProbabilityMeasure_gammaMeasure
    · have hi : (ij.1 : ℕ) + 1 ≤ p := ij.1.isLt
      have hi' : ((ij.1 : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hi
      linarith
    · norm_num
  · infer_instance

theorem bartlett_measure_probability {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    IsProbabilityMeasure (bartlettMeasure p α) := by
  let : ∀ ij : Fin p × Fin p, IsProbabilityMeasure (bartlettCoordinate α ij) :=
    bartlett_coordinate_probability hα
  unfold bartlettMeasure
  infer_instance

theorem bartlett_law_probability {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α)
    (S : Matrix (Fin p) (Fin p) ℝ) : IsProbabilityMeasure (bartlettLaw α S) := by
  let : IsProbabilityMeasure (bartlettMeasure p α) := bartlett_measure_probability hα
  unfold bartlettLaw
  infer_instance

theorem measurable_bartlettMatrix {p : ℕ} :
    Measurable (bartlettMatrix (p := p)) := by
  apply Measurable.of_eval_matrix
  intro i j
  unfold bartlettMatrix
  split_ifs <;> fun_prop

theorem measurable_bartlettValue {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ) :
    Measurable (bartlettValue S) := by
  have hb := measurable_bartlettMatrix (p := p)
  have hq : Measurable (fun x => CFC.sqrt S * bartlettMatrix x) := by
    apply Measurable.of_eval_matrix
    intro i j
    simp only [Matrix.mul_apply]
    apply Finset.measurable_sum
    intro k _
    exact measurable_const.mul (hb.eval_matrix (i := k) (j := j))
  apply Measurable.of_eval_matrix
  intro i j
  simp only [bartlettValue, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.measurable_sum
  intro k _
  exact (hq.eval_matrix (i := i) (j := k)).mul (hq.eval_matrix (i := j) (j := k))

theorem bartlettValue_positiveSemidefinite {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (x : Fin p × Fin p → ℝ) : (bartlettValue S x).PosSemidef := by
  simpa only [bartlettValue, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (CFC.sqrt S * bartlettMatrix x)

theorem bartlettLaw_positiveSemidefinite {p : ℕ} (α : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) :
    ∀ᵐ W ∂(bartlettLaw α S), W.PosSemidef := by
  unfold bartlettLaw
  rw [ae_map_iff (measurable_bartlettValue S).aemeasurable
    Matrix.posSemidef_is_closed.measurableSet]
  exact ae_of_all _ (bartlettValue_positiveSemidefinite S)

end ResearchMain.WishartBlocks
