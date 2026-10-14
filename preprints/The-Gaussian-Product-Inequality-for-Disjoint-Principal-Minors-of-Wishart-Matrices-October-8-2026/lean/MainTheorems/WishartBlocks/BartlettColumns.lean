import MainTheorems.WishartBlocks.BartlettLaw
import MainTheorems.WishartBlocks.PiGrouping

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

theorem bartlett_column_product_integral {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) (f : Fin p → (Fin p → ℝ) → ℝ) :
    ∫ x, ∏ j, f j (fun i => x (i, j)) ∂(bartlettMeasure p α) =
      ∏ j, ∫ x : Fin p → ℝ, f j x ∂(Measure.pi fun i => bartlettCoordinate α (i, j)) := by
  let : ∀ ij : Fin p × Fin p, IsProbabilityMeasure (bartlettCoordinate α ij) :=
    bartlett_coordinate_probability hα
  let e := (Equiv.sigmaEquivProd (Fin p) (Fin p)).trans (Equiv.prodComm _ _)
  have hflat := measurePreserving_piCongrLeft
    (fun ij : Fin p × Fin p => bartlettCoordinate α ij) e
  have hgroup := finite_pi_curry (fun j i : Fin p => bartlettCoordinate α (i, j))
  calc
    _ = ∫ x : (Σ _ : Fin p, Fin p) → ℝ, ∏ j, f j (fun i => x ⟨j, i⟩)
        ∂(Measure.pi fun ji => bartlettCoordinate α (ji.2, ji.1)) := by
      simpa [bartlettMeasure, e, MeasurableEquiv.coe_piCongrLeft,
        Equiv.piCongrLeft_apply, Equiv.symm_trans_apply, Equiv.prodComm_apply,
        Equiv.prodComm_symm, Equiv.trans_apply, Equiv.sigmaEquivProd_apply,
        Equiv.sigmaEquivProd_symm_apply] using
          (hflat.integral_comp' (fun x => ∏ j, f j (fun i => x (i, j)))).symm
    _ = ∫ x : Fin p → Fin p → ℝ, ∏ j, f j (x j)
        ∂(Measure.pi fun j => Measure.pi fun i => bartlettCoordinate α (i, j)) := by
      exact hgroup.integral_comp' (fun x => ∏ j, f j (x j))
    _ = _ := integral_fintype_prod_eq_prod f

noncomputable def bartlettColumn {p : ℕ} (j : Fin p) (x : Fin p → ℝ) : Fin p → ℝ :=
  fun i => if i = j then Real.sqrt (x i) else if j < i then x i else 0

theorem bartlettMatrix_column {p : ℕ} (x : Fin p × Fin p → ℝ) (i j : Fin p) :
    bartlettMatrix x i j = bartlettColumn j (fun k => x (k, j)) i := rfl

theorem trace_gram_columns {p : ℕ} (T B : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (T * (B * B.transpose)) =
      ∑ j, (fun i => B i j) ⬝ᵥ (T *ᵥ fun i => B i j) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    dotProduct, Matrix.mulVec]

theorem bartlett_gram_laplace_product {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) (T : Matrix (Fin p) (Fin p) ℝ) :
    ∫ x, Real.exp (-Matrix.trace (T * (bartlettMatrix x * (bartlettMatrix x).transpose)))
        ∂(bartlettMeasure p α) =
      ∏ j, ∫ x : Fin p → ℝ,
        Real.exp (-(bartlettColumn j x ⬝ᵥ (T *ᵥ bartlettColumn j x)))
        ∂(Measure.pi fun i => bartlettCoordinate α (i, j)) := by
  simp_rw [trace_gram_columns, bartlettMatrix_column, ← Finset.sum_neg_distrib, Real.exp_sum]
  exact bartlett_column_product_integral hα
    (fun j x => Real.exp (-(bartlettColumn j x ⬝ᵥ (T *ᵥ bartlettColumn j x))))

end ResearchMain.WishartBlocks
