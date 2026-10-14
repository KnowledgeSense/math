import MainTheorems.WishartBlocks.SpectralLaw.CholeskyChangeOfVariables
import MainTheorems.WishartBlocks.BartlettSupport
import MainTheorems.WishartBlocks.PiGrouping

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory

noncomputable def lowerCoordinateTransform {n : ℕ} (e : LowerIndex n) (t : ℝ) : ℝ :=
  if e.val.1 = e.val.2 then Real.sqrt t else t

noncomputable def bartlettLowerInput {n : ℕ} (x : Fin n × Fin n → ℝ) :
    LowerIndex n → ℝ := fun e => lowerCoordinateTransform e (x (ofLex e.val))

noncomputable def bartlettLowerLaw {n : ℕ} (α : ℝ) : Measure (LowerIndex n → ℝ) :=
  Measure.pi fun e : LowerIndex n =>
    (bartlettCoordinate α (ofLex e.val)).map (lowerCoordinateTransform e)

@[fun_prop] theorem measurable_lowerCoordinateTransform {n : ℕ} (e : LowerIndex n) :
    Measurable (lowerCoordinateTransform e) := by
  unfold lowerCoordinateTransform
  split_ifs <;> fun_prop

@[fun_prop] theorem measurable_bartlettLowerInput (n : ℕ) :
    Measurable (bartlettLowerInput (n := n)) := by
  apply Measurable.of_eval
  intro e
  exact (measurable_lowerCoordinateTransform e).comp (measurable_pi_apply (ofLex e.val))

theorem bartlettLowerInput_map {n : ℕ} {α : ℝ} (hα : (n : ℝ) - 1 < α) :
    (bartlettMeasure n α).map bartlettLowerInput = bartlettLowerLaw (n := n) α := by
  let : ∀ ij : Fin n × Fin n, IsProbabilityMeasure (bartlettCoordinate α ij) :=
    bartlett_coordinate_probability hα
  have hselect : (bartlettMeasure n α).map
      (fun (x : Fin n × Fin n → ℝ) (e : LowerIndex n) => x (ofLex e.val)) =
      Measure.pi (fun e : LowerIndex n => bartlettCoordinate α (ofLex e.val)) := by
    exact finite_pi_injection _ _ (fun e f h => Subtype.ext (congrArg toLex h))
  have htransform := Measure.pi_map_pi
    (μ := fun e : LowerIndex n => bartlettCoordinate α (ofLex e.val))
    (f := fun e => lowerCoordinateTransform e)
    (fun e => (measurable_lowerCoordinateTransform e).aemeasurable)
  unfold bartlettLowerLaw
  rw [← htransform, ← hselect, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem lowerMatrix_bartlettLowerInput {n : ℕ} (x : Fin n × Fin n → ℝ) :
    lowerMatrix (bartlettLowerInput x) = bartlettMatrix x := by
  ext i j
  unfold lowerMatrix lowerEntry
  by_cases hij : i = j
  · subst j
    simp only [le_refl, dite_true, ContinuousLinearMap.proj_apply,
      bartlettLowerInput, lowerCoordinateTransform, bartlettMatrix, ite_true, ofLex_toLex]
    change (if i = i then Real.sqrt (x (i, i)) else x (i, i)) = Real.sqrt (x (i, i))
    simp only [ite_true]
  · by_cases hji : j ≤ i
    · have hlt : j < i := lt_of_le_of_ne hji (Ne.symm hij)
      simp only [hji, dite_true, ContinuousLinearMap.proj_apply,
        bartlettLowerInput, lowerCoordinateTransform, bartlettMatrix,
        hij, hlt, ite_false, ite_true, ofLex_toLex]
      change (if i = j then Real.sqrt (x (i, j)) else x (i, j)) = x (i, j)
      exact ite_eq_right hij
    · have hlt : ¬j < i := fun h => hji h.le
      simp only [hji, dite_false, zero_apply,
        bartlettMatrix, hij, hlt, ite_false]

theorem bartlettLaw_isotropic_triangular_map {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) :
    (bartlettLowerLaw (n := n) α).map
      (fun x => lowerMatrix x * (lowerMatrix x).transpose) =
      bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hm : Measurable (fun x : LowerIndex n → ℝ =>
      lowerMatrix x * (lowerMatrix x).transpose) := by
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun x : LowerIndex n → ℝ =>
      ∑ k : Fin n, lowerMatrix x i k * lowerMatrix x j k)
    exact Finset.measurable_sum _ fun k _ =>
      ((continuous_lowerMatrix n).measurable.eval_matrix (i := i) (j := k)).mul
        ((continuous_lowerMatrix n).measurable.eval_matrix (i := j) (j := k))
  rw [← bartlettLowerInput_map hα,
    Measure.map_map hm (measurable_bartlettLowerInput n)]
  unfold bartlettLaw
  congr 1
  funext x
  simp only [Function.comp_apply, lowerMatrix_bartlettLowerInput,
    bartlettValue, CFC.sqrt_one, one_mul]

theorem bartlettLowerLaw_ae_positive {n : ℕ} {α : ℝ} (hα : (n : ℝ) - 1 < α) :
    ∀ᵐ x ∂bartlettLowerLaw (n := n) α, x ∈ positiveLowerCoordinates n := by
  rw [← bartlettLowerInput_map hα]
  change ∀ᵐ x ∂(bartlettMeasure n α).map bartlettLowerInput,
    ∀ i, 0 < lowerMatrix x i i
  rw [ae_map_iff (measurable_bartlettLowerInput n).aemeasurable
    (measurableSet_positiveLowerCoordinates n)]
  filter_upwards [bartlett_diagonal_ae_positive hα] with x hx
  intro i
  rw [lowerMatrix_bartlettLowerInput]
  simp only [bartlettMatrix, ite_true]
  exact Real.sqrt_pos.mpr (hx i)

end ResearchMain.WishartBlocks
