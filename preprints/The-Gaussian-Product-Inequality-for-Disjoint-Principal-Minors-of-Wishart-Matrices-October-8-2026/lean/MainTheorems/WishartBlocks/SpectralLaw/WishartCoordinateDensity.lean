import MainTheorems.WishartBlocks.SpectralLaw.BartlettDensityAlgebra

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable def wishartDensityReal {n : ℕ} (α : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  wishartDensityCoefficient n α * W.det ^ ((α - n - 1) / 2) * Real.exp (-W.trace / 2)

noncomputable def wishartCoordinateDensity {n : ℕ} (α : ℝ)
    (y : LowerIndex n → ℝ) : ℝ≥0∞ :=
  (positiveSymmetricCoordinates n).indicator
    (fun z => ENNReal.ofReal (wishartDensityReal α (symmetricMatrix z))) y

theorem measurableSet_positiveSymmetricCoordinates (n : ℕ) :
    MeasurableSet (positiveSymmetricCoordinates n) :=
  (measurableSet_positiveDefinite n).preimage (symmetricMatrix_continuous n).measurable

theorem measurable_wishartDensityReal (n : ℕ) (α : ℝ) :
    Measurable (wishartDensityReal (n := n) α) := by
  unfold wishartDensityReal
  fun_prop

theorem measurable_wishartCoordinateDensity (n : ℕ) (α : ℝ) :
    Measurable (wishartCoordinateDensity (n := n) α) := by
  exact (((measurable_wishartDensityReal n α).comp
    (symmetricMatrix_continuous n).measurable).ennreal_ofReal).indicator
      (measurableSet_positiveSymmetricCoordinates n)

theorem wishartDensityReal_pos {n : ℕ} {α : ℝ} (hα : (n : ℝ) - 1 < α)
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.PosDef) : 0 < wishartDensityReal α W :=
  mul_pos (mul_pos (wishartDensityCoefficient_pos hα) (Real.rpow_pos_of_pos hW.det_pos _))
    (Real.exp_pos _)

@[fun_prop] theorem measurable_symmetricCoordinates (n : ℕ) :
    Measurable (symmetricCoordinates (n := n)) := by
  unfold symmetricCoordinates
  fun_prop

@[fun_prop] theorem measurable_choleskyCoordinates (n : ℕ) :
    Measurable (choleskyCoordinates (n := n)) := by
  apply Measurable.of_eval
  intro e
  change Measurable (fun x : LowerIndex n → ℝ =>
    ∑ k : Fin n, lowerMatrix x e.val.1 k * lowerMatrix x e.val.2 k)
  exact Finset.measurable_sum _ fun k _ =>
    ((continuous_lowerMatrix n).measurable.eval_matrix (i := e.val.1) (j := k)).mul
      ((continuous_lowerMatrix n).measurable.eval_matrix (i := e.val.2) (j := k))

@[fun_prop] theorem measurable_lowerGram (n : ℕ) :
    Measurable (fun x : LowerIndex n → ℝ => lowerMatrix x * (lowerMatrix x).transpose) := by
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun x : LowerIndex n → ℝ =>
    ∑ k : Fin n, lowerMatrix x i k * lowerMatrix x j k)
  exact Finset.measurable_sum _ fun k _ =>
    ((continuous_lowerMatrix n).measurable.eval_matrix (i := i) (j := k)).mul
      ((continuous_lowerMatrix n).measurable.eval_matrix (i := j) (j := k))

theorem lowerBartlettPDF_cholesky_raw {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) {x : LowerIndex n → ℝ}
    (hx : x ∈ positiveLowerCoordinates n) :
    lowerBartlettPDF α x = ENNReal.ofReal (choleskyJacobianWeight x) *
      ENNReal.ofReal (wishartDensityReal α (symmetricMatrix (choleskyCoordinates x))) := by
  rw [lowerBartlettPDF_cholesky hα hx, symmetricMatrix_choleskyCoordinates]
  unfold wishartDensityReal
  rw [show choleskyJacobianWeight x * wishartDensityCoefficient n α *
      (lowerMatrix x * (lowerMatrix x).transpose).det ^ ((α - n - 1) / 2) *
      Real.exp (-(lowerMatrix x * (lowerMatrix x).transpose).trace / 2) =
      choleskyJacobianWeight x *
        (wishartDensityCoefficient n α *
          (lowerMatrix x * (lowerMatrix x).transpose).det ^ ((α - n - 1) / 2) *
          Real.exp (-(lowerMatrix x * (lowerMatrix x).transpose).trace / 2)) by ring]
  exact ENNReal.ofReal_mul (choleskyJacobianWeight_pos hx).le

theorem bartlett_cholesky_lintegral {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) {f : (LowerIndex n → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂(bartlettLowerLaw (n := n) α).map choleskyCoordinates) =
      ∫⁻ y, wishartCoordinateDensity α y * f y := by
  rw [lintegral_map hf (measurable_choleskyCoordinates n),
    ← Measure.restrict_eq_self_of_ae_mem (bartlettLowerLaw_ae_positive hα),
    bartlettLowerLaw_density hα]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul volume
      (f := lowerBartlettPDF α) (g := fun x => f (choleskyCoordinates x))
      (measurable_lowerBartlettPDF n α)
      (hf.comp (measurable_choleskyCoordinates n))
      (measurableSet_positiveLowerCoordinates n)]
  calc
    _ = ∫⁻ x in positiveLowerCoordinates n,
        ENNReal.ofReal (choleskyJacobianWeight x) *
          (ENNReal.ofReal (wishartDensityReal α (symmetricMatrix (choleskyCoordinates x))) *
            f (choleskyCoordinates x)) := by
      apply setLIntegral_congr_fun (measurableSet_positiveLowerCoordinates n)
      intro x hx
      rw [Pi.mul_apply, lowerBartlettPDF_cholesky_raw hα hx, mul_assoc]
    _ = ∫⁻ y in positiveSymmetricCoordinates n,
        ENNReal.ofReal (wishartDensityReal α (symmetricMatrix y)) * f y :=
      (cholesky_lintegral_changeOfVariables (n := n)
        (fun y => ENNReal.ofReal (wishartDensityReal α (symmetricMatrix y)) * f y)).symm
    _ = _ := by
      unfold wishartCoordinateDensity
      simp_rw [← Set.indicator_mul_left]
      exact (lintegral_indicator (measurableSet_positiveSymmetricCoordinates n) _).symm

theorem bartlettLaw_isotropic_coordinate_map {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) :
    (bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ)).map symmetricCoordinates =
      (bartlettLowerLaw (n := n) α).map choleskyCoordinates := by
  rw [← bartlettLaw_isotropic_triangular_map hα,
    Measure.map_map (measurable_symmetricCoordinates n) (measurable_lowerGram n)]
  rfl

theorem bartlettLaw_isotropic_coordinate_density {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) :
    (bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ)).map symmetricCoordinates =
      volume.withDensity (wishartCoordinateDensity α) := by
  rw [bartlettLaw_isotropic_coordinate_map hα]
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_withDensity_eq_lintegral_mul volume (measurable_wishartCoordinateDensity n α) hf]
  exact bartlett_cholesky_lintegral hα hf

theorem bartlettLaw_isotropic_symmetric_density {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) :
    (volume.withDensity (wishartCoordinateDensity (n := n) α)).map symmetricMatrix =
      bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [← bartlettLaw_isotropic_coordinate_density hα,
    Measure.map_map (symmetricMatrix_continuous n).measurable
      (measurable_symmetricCoordinates n)]
  have he : (symmetricMatrix ∘ symmetricCoordinates) =ᵐ[
        bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ)] id := by
    filter_upwards [bartlettLaw_positiveDefinite hα Matrix.PosDef.one] with W hW
    exact symmetricMatrix_symmetricCoordinates hW.isHermitian
  rw [Measure.map_congr he, Measure.map_id]

end ResearchMain.WishartBlocks
