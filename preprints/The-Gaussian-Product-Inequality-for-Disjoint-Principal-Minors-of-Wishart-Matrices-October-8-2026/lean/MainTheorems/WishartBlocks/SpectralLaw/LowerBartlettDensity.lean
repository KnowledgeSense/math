import MainTheorems.WishartBlocks.SpectralLaw.TriangularBartlettLaw
import MainTheorems.WishartBlocks.SpectralLaw.GammaSquareRootDensity
import MainTheorems.WishartBlocks.SpectralLaw.FiniteDensityProducts

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable def lowerCoordinatePDF {n : ℕ} (α : ℝ)
    (e : LowerIndex n) (t : ℝ) : ℝ≥0∞ :=
  if e.val.1 = e.val.2 then sqrtGammaPDF ((α - e.val.1.val) / 2) (1 / 2) t
  else gaussianPDF 0 1 t

theorem measurable_lowerCoordinatePDF {n : ℕ} (α : ℝ) (e : LowerIndex n) :
    Measurable (lowerCoordinatePDF α e) := by
  unfold lowerCoordinatePDF
  split_ifs
  · unfold sqrtGammaPDF
    exact Measurable.ite measurableSet_Ioi
      ((measurable_const.mul measurable_id).ennreal_ofReal.mul
        (((measurable_gammaPDFReal _ _).ennreal_ofReal).comp (measurable_id.pow_const 2)))
      measurable_const
  · exact measurable_gaussianPDF 0 1

theorem lowerCoordinate_density {n : ℕ} (α : ℝ) (e : LowerIndex n) :
    (bartlettCoordinate α (ofLex e.val)).map (lowerCoordinateTransform e) =
      volume.withDensity (lowerCoordinatePDF α e) := by
  unfold bartlettCoordinate lowerCoordinateTransform lowerCoordinatePDF
  have hi : (ofLex e.val).1 = e.val.1 := rfl
  have hj : (ofLex e.val).2 = e.val.2 := rfl
  simp only [hi, hj]
  by_cases he : e.val.1 = e.val.2
  · simp only [he, ite_true]
    exact sqrt_gamma_density _ _
  · simp only [he, ite_false]
    change (gaussianReal 0 1).map id = volume.withDensity (gaussianPDF 0 1)
    rw [Measure.map_id]
    exact gaussianReal_of_var_ne_zero 0 (v := 1) (by norm_num)

noncomputable def lowerBartlettPDF {n : ℕ} (α : ℝ) (x : LowerIndex n → ℝ) : ℝ≥0∞ :=
  ∏ e, lowerCoordinatePDF α e (x e)

theorem measurable_lowerBartlettPDF (n : ℕ) (α : ℝ) :
    Measurable (lowerBartlettPDF (n := n) α) := by
  unfold lowerBartlettPDF
  exact Finset.measurable_prod _ fun e _ =>
    (measurable_lowerCoordinatePDF α e).comp (measurable_pi_apply e)

theorem bartlettLowerLaw_density {n : ℕ} {α : ℝ} (hα : (n : ℝ) - 1 < α) :
    bartlettLowerLaw (n := n) α = volume.withDensity (lowerBartlettPDF α) := by
  let : ∀ e : LowerIndex n,
      IsProbabilityMeasure (volume.withDensity (lowerCoordinatePDF α e)) := fun e => by
    rw [← lowerCoordinate_density α e]
    let := bartlett_coordinate_probability hα (ofLex e.val)
    infer_instance
  unfold bartlettLowerLaw lowerBartlettPDF
  simp_rw [lowerCoordinate_density]
  exact pi_withDensity_finite (fun _ => volume) _ (fun e => measurable_lowerCoordinatePDF α e)

theorem cholesky_lintegral_changeOfVariables {n : ℕ}
    (g : (LowerIndex n → ℝ) → ℝ≥0∞) :
    (∫⁻ y in positiveSymmetricCoordinates n, g y) =
      ∫⁻ x in positiveLowerCoordinates n,
        ENNReal.ofReal (choleskyJacobianWeight x) * g (choleskyCoordinates x) := by
  rw [← choleskyCoordinates_image_positive]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (measurableSet_positiveLowerCoordinates n)
    (fun x _ => (choleskyCoordinates_hasFDerivAt x).hasFDerivWithinAt)
    choleskyCoordinates_injOn_positive]
  apply setLIntegral_congr_fun (measurableSet_positiveLowerCoordinates n)
  intro x hx
  change ENNReal.ofReal |(choleskyDerivative x).det| * g (choleskyCoordinates x) =
    ENNReal.ofReal (choleskyJacobianWeight x) * g (choleskyCoordinates x)
  rw [choleskyDerivative_det_eq_weight, abs_of_pos (choleskyJacobianWeight_pos hx)]

theorem bartlettLaw_isotropic_lower_density {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) :
    (volume.withDensity (lowerBartlettPDF (n := n) α)).map
        (fun x => lowerMatrix x * (lowerMatrix x).transpose) =
      bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [← bartlettLowerLaw_density hα]
  exact bartlettLaw_isotropic_triangular_map hα

end ResearchMain.WishartBlocks
