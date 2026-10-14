import MainTheorems.AHOConstants.TracePositivity
import MainTheorems.AHOConstants.SchattenTrace

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem positive_trace_nonneg {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    0 ≤ (Matrix.trace A).re := by
  rw [hA.isHermitian.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum]
  exact Finset.sum_nonneg (fun i _ => hA.eigenvalues_nonneg i)

theorem positive_trace_norm {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    ‖Matrix.trace A‖ = (Matrix.trace A).re := by
  rw [hA.isHermitian.trace_eq_sum_eigenvalues]
  change ‖∑ i, (hA.isHermitian.eigenvalues i : ℂ)‖ =
    (∑ i, (hA.isHermitian.eigenvalues i : ℂ)).re
  have he : (∑ i, (hA.isHermitian.eigenvalues i : ℂ)) =
      ((∑ i, hA.isHermitian.eigenvalues i : ℝ) : ℂ) := by norm_cast
  rw [he]
  simp only [Complex.norm_real, Complex.ofReal_re]
  exact Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => hA.eigenvalues_nonneg i))

theorem positive_trace_pos [Nonempty I] {A : Matrix I I ℂ} (hA : A.PosDef) :
    0 < (Matrix.trace A).re := by
  simpa only [Matrix.mul_one] using
    trace_product_positive hA (Matrix.PosDef.one (n := I) (R := ℂ))

theorem trace_product_norm_positive [Nonempty I] {A B : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    ‖Matrix.trace (A * B)‖ = (Matrix.trace (A * B)).re := by
  have hs : star (Matrix.trace (A * B)) = Matrix.trace (A * B) := by
    rw [← Matrix.trace_conjTranspose, ← Matrix.star_eq_conjTranspose, star_mul,
      hA.isHermitian.isSelfAdjoint.star_eq, hB.isHermitian.isSelfAdjoint.star_eq,
      Matrix.trace_mul_comm]
  have he : (((Matrix.trace (A * B)).re : ℝ) : ℂ) = Matrix.trace (A * B) :=
    RCLike.conj_eq_iff_re.mp (by simpa only [RCLike.star_def] using hs)
  rw [← he]
  simp only [Complex.norm_real, Complex.ofReal_re]
  exact Real.norm_of_nonneg (trace_product_positive hA hB).le

end ResearchMain.AHOConstants
