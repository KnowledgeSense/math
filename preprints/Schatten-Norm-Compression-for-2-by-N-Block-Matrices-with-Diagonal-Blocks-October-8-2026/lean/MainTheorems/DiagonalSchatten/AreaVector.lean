import MainTheorems.DiagonalSchatten.GramFiber
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

def areaVector (X : Matrix (Fin 2) J ℝ) : EuclideanSpace ℝ (J × J) :=
  WithLp.toLp 2 fun jk => X 0 jk.1 * X 1 jk.2 - X 1 jk.1 * X 0 jk.2

theorem minor_sum_sq (u v : J → ℝ) :
    (∑ j, ∑ k, (u j * v k - v j * u k) ^ 2) =
      2 * ((∑ j, u j ^ 2) * (∑ j, v j ^ 2) - (∑ j, u j * v j) ^ 2) := by
  have hterm (j k : J) :
      (u j * v k - v j * u k) ^ 2 = u j ^ 2 * v k ^ 2 + v j ^ 2 * u k ^ 2 -
        2 * (u j * v j) * (u k * v k) := by ring
  calc
    _ = ∑ j, ∑ k, (u j ^ 2 * v k ^ 2 + v j ^ 2 * u k ^ 2 -
        2 * (u j * v j) * (u k * v k)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      exact hterm j k
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring

theorem areaVector_norm_sq (X : Matrix (Fin 2) J ℝ) :
    ‖areaVector X‖ ^ 2 = 2 * (gramFirst X * gramSecond X - gramCross X ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [areaVector, PiLp.toLp_apply, Fintype.sum_prod_type]
  exact minor_sum_sq (fun j => X 0 j) (fun j => X 1 j)

theorem contDiff_areaVector : ContDiff ℝ 1 (areaVector (J := J)) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : J × J => ℝ)
  change ContDiff ℝ 1 (fun X : Matrix (Fin 2) J ℝ =>
    e.symm (fun jk => X 0 jk.1 * X 1 jk.2 - X 1 jk.1 * X 0 jk.2))
  exact e.symm.contDiff.comp (by fun_prop)

theorem contDiff_areaVector_norm_rpow {p : ℝ} (hp : 1 < p) :
    ContDiff ℝ 1 (fun X : Matrix (Fin 2) J ℝ => ‖areaVector X‖ ^ p) :=
  contDiff_areaVector.norm_rpow hp

end

end ResearchMain.DiagonalSchatten
