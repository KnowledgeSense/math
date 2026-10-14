import MainTheorems.AHOConstants.RankOneTrace
import MainTheorems.AHOConstants.TwoProjectionPowers

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

def realVector (u : I → ℝ) : I → ℂ := fun i => (u i : ℂ)

def realProjection (u : I → ℝ) : Matrix I I ℂ := rankOne (realVector u) (realVector u)

omit [DecidableEq I] in
theorem real_vector_pairing (u v : I → ℝ) :
    vectorPairing (realVector u) (realVector v) = ((∑ i, u i * v i : ℝ) : ℂ) := by
  unfold vectorPairing realVector
  norm_cast

omit [DecidableEq I] in
theorem realProjection_posSemidef (u : I → ℝ) : (realProjection u).PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star (realVector u)
  have he : Matrix.vecMulVec (realVector u) (star (realVector u)) = realProjection u := by
    ext i j
    change (u i : ℂ) * star (u j : ℂ) = (u i : ℂ) * (u j : ℂ)
    simp
  rw [he] at h
  exact h

omit [DecidableEq I] in
theorem realProjection_idempotent {u : I → ℝ} (hu : (∑ i, u i ^ 2) = 1) :
    realProjection u * realProjection u = realProjection u := by
  have hn : vectorPairing (realVector u) (realVector u) = 1 := by
    rw [real_vector_pairing]
    simp only [← pow_two, hu, Complex.ofReal_one]
  unfold realProjection
  rw [rankOne_mul, hn, one_smul]

omit [DecidableEq I] in
theorem realProjection_orthogonal {u v : I → ℝ} (huv : (∑ i, u i * v i) = 0) :
    realProjection u * realProjection v = 0 := by
  unfold realProjection
  rw [rankOne_mul, real_vector_pairing, huv, Complex.ofReal_zero, zero_smul]

omit [DecidableEq I] in
theorem realProjection_trace (u : I → ℝ) :
    Matrix.trace (realProjection u) = ((∑ i, u i ^ 2 : ℝ) : ℂ) := by
  rw [realProjection, rankOne_trace, real_vector_pairing]
  simp only [pow_two]

omit [DecidableEq I] in
theorem realProjection_product_trace (u v : I → ℝ) :
    Matrix.trace (realProjection u * realProjection v) =
      (((∑ i, u i * v i) ^ 2 : ℝ) : ℂ) := by
  unfold realProjection
  rw [rankOne_mul, Matrix.trace_smul, rankOne_trace, real_vector_pairing]
  simp only [smul_eq_mul, pow_two, Complex.ofReal_mul]

end ResearchMain.AHOConstants
