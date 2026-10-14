import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def schattenPower (p : ℝ) (A : Matrix I J ℂ) : ℝ :=
  ∑ i : Fin (Fintype.card J), (A.toEuclideanLin.singularValues i) ^ p

noncomputable def schattenNorm (p : ℝ) (A : Matrix I J ℂ) : ℝ :=
  (schattenPower p A) ^ (1 / p)

omit [DecidableEq I] in
theorem schattenPower_zero {p : ℝ} (hp : p ≠ 0) :
    schattenPower p (0 : Matrix I J ℂ) = 0 := by
  simp [schattenPower, LinearMap.singularValues_zero, Real.zero_rpow hp]

omit [DecidableEq I] in
theorem schattenPower_nonneg (p : ℝ) (A : Matrix I J ℂ) :
    0 ≤ schattenPower p A := by
  unfold schattenPower
  exact Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (A.toEuclideanLin.singularValues_nonneg i) p

omit [DecidableEq I] in
theorem schattenNorm_nonneg (p : ℝ) (A : Matrix I J ℂ) :
    0 ≤ schattenNorm p A :=
  Real.rpow_nonneg (schattenPower_nonneg p A) _

omit [DecidableEq I] in
theorem schattenNorm_rpow (p : ℝ) (hp : p ≠ 0) (A : Matrix I J ℂ) :
    (schattenNorm p A) ^ p = schattenPower p A := by
  unfold schattenNorm
  rw [← Real.rpow_mul (schattenPower_nonneg p A), one_div_mul_cancel hp, Real.rpow_one]

theorem schattenPower_two (A : Matrix I J ℂ) :
    schattenPower 2 A = ∑ j, ∑ i, ‖A i j‖ ^ 2 := by
  unfold schattenPower
  simp_rw [Real.rpow_two,
    A.toEuclideanLin.sq_singularValues_fin finrank_euclideanSpace]
  rw [← A.toEuclideanLin.isSymmetric_adjoint_comp_self.re_trace_eq_sum_eigenvalues
    finrank_euclideanSpace]
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    ← Matrix.toLpLin_mul_same]
  rw [Matrix.toLpLin_eq_toLin, Matrix.trace_toLin_eq]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    map_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simpa [← Complex.ofReal_pow] using congrArg Complex.re (Complex.conj_mul' (A i j))

end ResearchMain.DiagonalSchatten
