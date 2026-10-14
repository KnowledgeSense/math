import MainTheorems.AHOConstants.SpectralPowers
import Mathlib.LinearAlgebra.Matrix.Trace

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem trace_product_diagonalization {A B : Matrix I I ℂ} (hB : B.IsHermitian) :
    Matrix.trace (A * B) = Matrix.trace
      (((star hB.eigenvectorUnitary : Matrix I I ℂ) * A *
        (hB.eigenvectorUnitary : Matrix I I ℂ)) *
        Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ))) := by
  let U : Matrix I I ℂ := hB.eigenvectorUnitary
  let D : Matrix I I ℂ := Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ))
  have hB' : B = U * D * star U := by
    simpa only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_eq_complex_ofReal,
      Function.comp_def] using hB.spectral_theorem
  calc
    Matrix.trace (A * B) = Matrix.trace ((A * (U * D)) * star U) := by
      rw [hB']
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (star U * (A * (U * D))) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((star U * A * U) * D) := by simp only [Matrix.mul_assoc]

theorem trace_product_positive [Nonempty I] {A B : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosDef) : 0 < (Matrix.trace (A * B)).re := by
  let U : Matrix I I ℂ := hB.isHermitian.eigenvectorUnitary
  let C : Matrix I I ℂ := star U * A * U
  have hU : IsUnit U := Unitary.isUnit_coe
  have hC : C.PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff hU).mpr hA
  have hdiag : ∀ i, 0 < (C i i).re := fun i =>
    (RCLike.pos_iff.mp (hC.diag_pos (i := i))).1
  rw [trace_product_diagonalization hB.isHermitian]
  change 0 < (Matrix.trace (C * Matrix.diagonal
    (fun i => (hB.isHermitian.eigenvalues i : ℂ)))).re
  simp only [Matrix.mul_diagonal, Matrix.trace, Matrix.diag_apply, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact Finset.sum_pos (fun i _ => mul_pos (hdiag i) (hB.eigenvalues_pos i))
    Finset.univ_nonempty

end ResearchMain.AHOConstants
