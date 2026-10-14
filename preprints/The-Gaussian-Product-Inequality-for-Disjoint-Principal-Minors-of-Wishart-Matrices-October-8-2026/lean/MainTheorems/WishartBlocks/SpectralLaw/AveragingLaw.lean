import MainTheorems.WishartBlocks.SpectralLaw.OrthogonalHaar
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Matrix.MeasurableSpace

namespace ResearchMain.WishartBlocks

open MeasureTheory

theorem isotropic_congruence_joint_integrable {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : Measurable G)
    (hiG : Integrable G (bartlettLaw α 1)) :
    Integrable (fun z : Matrix.orthogonalGroup (Fin n) ℝ ×
        Matrix (Fin n) (Fin n) ℝ =>
      G (matrixCongruence (z.1 : Matrix (Fin n) (Fin n) ℝ) z.2))
      ((orthogonalHaar n).prod (bartlettLaw α 1)) := by
  let : IsProbabilityMeasure (bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ)) :=
    bartlett_law_probability hα 1
  have hm : Measurable (fun z : Matrix.orthogonalGroup (Fin n) ℝ ×
        Matrix (Fin n) (Fin n) ℝ =>
      matrixCongruence (z.1 : Matrix (Fin n) (Fin n) ℝ) z.2) := by
    have hU : Measurable (fun z : Matrix.orthogonalGroup (Fin n) ℝ ×
        Matrix (Fin n) (Fin n) ℝ => (z.1 : Matrix (Fin n) (Fin n) ℝ)) :=
      measurable_subtype_coe.comp measurable_fst
    apply Measurable.of_eval_matrix
    intro i j
    simp only [matrixCongruence, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.measurable_sum _ fun k _ =>
      (Finset.measurable_sum _ fun l _ =>
        (hU.eval_matrix (i := i) (j := l)).mul
          (measurable_snd.eval_matrix (i := l) (j := k))).mul
        (hU.eval_matrix (i := j) (j := k))
  apply (integrable_prod_iff (hG.comp hm).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun U => by
      have h := hiG
      rw [← bartlettLaw_isotropic_orthogonal_invariant hα U] at h
      exact h.comp_measurable (measurable_matrixCongruence _)
  · have he : (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
        ∫ W, ‖G (matrixCongruence (U : Matrix (Fin n) (Fin n) ℝ) W)‖
          ∂bartlettLaw α 1) = fun _ => ∫ W, ‖G W‖ ∂bartlettLaw α 1 := by
      funext U
      exact bartlettLaw_isotropic_integral_congruence hα U hG.norm
    change Integrable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ∫ W, ‖G (matrixCongruence (U : Matrix (Fin n) (Fin n) ℝ) W)‖
        ∂bartlettLaw α 1) (orthogonalHaar n)
    rw [he]
    exact integrable_const _

theorem bartlettLaw_isotropic_orthogonalAverage_integrable {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : Measurable G)
    (hiG : Integrable G (bartlettLaw α 1)) :
    Integrable (orthogonalAverage G) (bartlettLaw α 1) := by
  let : IsProbabilityMeasure (bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ)) :=
    bartlett_law_probability hα 1
  exact (isotropic_congruence_joint_integrable hα hG hiG).integral_prod_right

theorem bartlettLaw_isotropic_integral_orthogonalAverage {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : Measurable G)
    (hiG : Integrable G (bartlettLaw α 1)) :
    (∫ W, orthogonalAverage G W ∂bartlettLaw α 1) =
      ∫ W, G W ∂bartlettLaw α 1 := by
  let : IsProbabilityMeasure (bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ)) :=
    bartlett_law_probability hα 1
  unfold orthogonalAverage
  rw [← integral_integral_swap (isotropic_congruence_joint_integrable hα hG hiG)]
  simp_rw [bartlettLaw_isotropic_integral_congruence hα _ hG]
  simp

end ResearchMain.WishartBlocks
