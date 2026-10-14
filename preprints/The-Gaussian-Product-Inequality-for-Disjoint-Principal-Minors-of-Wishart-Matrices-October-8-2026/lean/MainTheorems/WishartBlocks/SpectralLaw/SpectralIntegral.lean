import MainTheorems.WishartBlocks.SpectralLaw.SortedAverage
import MainTheorems.WishartBlocks.SpectralLaw.AveragingLaw
import MainTheorems.WishartBlocks.BartlettSupport

namespace ResearchMain.WishartBlocks

open MeasureTheory
open scoped BigOperators

noncomputable def isotropicEigenvalueLaw (n : ℕ) (α : ℝ) : Measure (Fin n → ℝ) :=
  (bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ)).map (sortedEigenvalues n)

instance isotropicEigenvalueLaw_probability {n : ℕ} {α : ℝ}
    [IsProbabilityMeasure (bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ))] :
    IsProbabilityMeasure (isotropicEigenvalueLaw n α) := by
  unfold isotropicEigenvalueLaw
  infer_instance

theorem orthogonal_congruence_det {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (W : Matrix (Fin n) (Fin n) ℝ) :
    (matrixCongruence (U : Matrix (Fin n) (Fin n) ℝ) W).det = W.det := by
  have hu := congrArg Matrix.det (orthogonal_congruence_one U)
  simp only [matrixCongruence, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one,
    mul_one] at hu
  simp only [matrixCongruence, Matrix.det_mul, Matrix.det_transpose]
  calc
    _ = W.det * ((U : Matrix (Fin n) (Fin n) ℝ).det *
        (U : Matrix (Fin n) (Fin n) ℝ).det) := by ring
    _ = _ := by rw [hu, mul_one]

theorem orthogonalAverage_determinant_weight {n : ℕ} (ν : ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) :
    orthogonalAverage (fun V => V.det ^ ν * G V) W =
      W.det ^ ν * orthogonalAverage G W := by
  unfold orthogonalAverage
  simp_rw [orthogonal_congruence_det]
  exact integral_const_mul _ _

theorem measurable_orthogonalSpectralAverage {n : ℕ}
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : Measurable G) :
    Measurable (orthogonalSpectralAverage G) := by
  have hc : Continuous (fun p : (Fin n → ℝ) × Matrix.orthogonalGroup (Fin n) ℝ =>
      matrixCongruence (p.2 : Matrix (Fin n) (Fin n) ℝ)
        (Matrix.diagonal (positiveCoordinates p.1))) := by
    unfold matrixCongruence positiveCoordinates
    fun_prop
  exact (hG.comp hc.measurable).stronglyMeasurable.integral_prod_right'.measurable

theorem bartlettLaw_isotropic_determinant_average {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) (ν : ℝ)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : Measurable G)
    (hi : Integrable (fun W => W.det ^ ν * G W) (bartlettLaw α 1)) :
    (∫ W, W.det ^ ν * G W ∂bartlettLaw α 1) =
      ∫ W, W.det ^ ν * orthogonalAverage G W ∂bartlettLaw α 1 := by
  have hm : Measurable (fun W : Matrix (Fin n) (Fin n) ℝ => W.det ^ ν * G W) := by
    fun_prop
  simpa only [orthogonalAverage_determinant_weight] using
    (bartlettLaw_isotropic_integral_orthogonalAverage hα hm hi).symm

theorem bartlettLaw_isotropic_weighted_spectral_integral {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) (ν : ℝ)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : Measurable G)
    (hi : Integrable (fun W => W.det ^ ν * G W) (bartlettLaw α 1)) :
    (∫ W, W.det ^ ν * G W ∂bartlettLaw α 1) =
      ∫ lam, (∏ i : Fin n, lam i) ^ ν * orthogonalSpectralAverage G lam
        ∂isotropicEigenvalueLaw n α := by
  rw [bartlettLaw_isotropic_determinant_average hα ν hG hi,
    isotropicEigenvalueLaw,
    integral_map (f := fun lam : Fin n → ℝ =>
      (∏ i : Fin n, lam i) ^ ν * orthogonalSpectralAverage G lam)
      (measurable_sortedEigenvalues n).aemeasurable
      ((by fun_prop : Measurable (fun lam : Fin n → ℝ => (∏ i, lam i) ^ ν)).mul
        (measurable_orthogonalSpectralAverage hG)).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [bartlettLaw_positiveDefinite hα Matrix.PosDef.one] with W hW
  rw [← sortedEigenvalues_det hW.isHermitian,
    ← orthogonalAverage_eq_sortedSpectralAverage G hW.posSemidef]

end ResearchMain.WishartBlocks
