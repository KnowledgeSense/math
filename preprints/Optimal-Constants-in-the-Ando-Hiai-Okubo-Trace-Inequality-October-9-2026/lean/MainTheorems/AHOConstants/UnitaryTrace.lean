import MainTheorems.AHOConstants.TracePositivity
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem unitary_positive_trace_bound {U P : Matrix I I ℂ}
    (hU : U ∈ unitary (Matrix I I ℂ)) (hP : P.PosSemidef) :
    ‖Matrix.trace (U * P)‖ ≤ (Matrix.trace P).re := by
  let V : Matrix I I ℂ := hP.isHermitian.eigenvectorUnitary
  let C : Matrix I I ℂ := star V * U * V
  have hV : V ∈ unitary (Matrix I I ℂ) := hP.isHermitian.eigenvectorUnitary.prop
  have hC : C ∈ unitary (Matrix I I ℂ) :=
    (unitary (Matrix I I ℂ)).mul_mem
      ((unitary (Matrix I I ℂ)).mul_mem (Unitary.star_mem hV) hU) hV
  have hdiag : ∀ i, ‖C i i‖ ≤ 1 := fun i => entry_norm_bound_of_unitary hC i i
  rw [trace_product_diagonalization hP.isHermitian,
    hP.isHermitian.trace_eq_sum_eigenvalues]
  change ‖Matrix.trace (C * Matrix.diagonal
    (fun i => (hP.isHermitian.eigenvalues i : ℂ)))‖ ≤
    (∑ i, (hP.isHermitian.eigenvalues i : ℂ)).re
  simp only [Matrix.mul_diagonal, Matrix.trace, Matrix.diag_apply, Complex.re_sum, Complex.ofReal_re]
  calc
    ‖∑ i, C i i * (hP.isHermitian.eigenvalues i : ℂ)‖ ≤
        ∑ i, ‖C i i * (hP.isHermitian.eigenvalues i : ℂ)‖ := norm_sum_le _ _
    _ = ∑ i, ‖C i i‖ * hP.isHermitian.eigenvalues i := by
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hP.eigenvalues_nonneg _)]
    _ ≤ ∑ i, hP.isHermitian.eigenvalues i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_of_le_one_left (hP.eigenvalues_nonneg i) (hdiag i)

end ResearchMain.AHOConstants
