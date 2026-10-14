import MainTheorems.DiagonalSchatten.SpectralJacobian
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators

theorem normalizedSpectralJacobian_row_sum (p H h t w : ℝ) (i : Fin 3) :
    ∑ j, normalizedSpectralJacobian p H h t w i j = 0 := by
  fin_cases i <;>
    simp [Fin.sum_univ_four,
      normalizedSpectralJacobian, spectralChartEntries, spectralChartTangentT,
      spectralChartTangentW, spectralChartTangentH] <;> ring

theorem normalizedSpectralJacobian_kernel {p h t w : ℝ}
    (hp : 1 < p) (hp2 : p ≠ 2) (hh : 0 < h) (hh1 : h < 1)
    (ht : 0 < t) (hw : 0 < w) (z : Fin 4 → ℝ)
    (hz : (normalizedSpectralJacobian p (h ^ (p - 1)) h t w).mulVec z = 0) :
    ∀ j, z j = z 3 := by
  let M := normalizedSpectralJacobian p (h ^ (p - 1)) h t w
  let N := spectralJacobianMinor p (h ^ (p - 1)) h t w
  let u : Fin 3 → ℝ := fun j => z j.castSucc - z 3
  have hNu : N.mulVec u = 0 := by
    funext i
    have hrow := normalizedSpectralJacobian_row_sum p (h ^ (p - 1)) h t w i
    have he := congrFun hz i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.zero_apply] at he
    simp only [Fin.sum_univ_four] at hrow
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.zero_apply]
    change M i 0 * (z 0 - z 3) + M i 1 * (z 1 - z 3) +
      M i 2 * (z 2 - z 3) = 0
    dsimp [M] at *
    linear_combination he - z 3 * hrow
  have hu := Matrix.eq_zero_of_mulVec_eq_zero
    (spectralJacobianMinor_ne_zero hp hp2 hh hh1 ht hw) hNu
  intro j
  fin_cases j
  · change z 0 = z 3
    have h := congrFun hu 0
    dsimp [u] at h
    linarith
  · change z 1 = z 3
    have h := congrFun hu 1
    dsimp [u] at h
    linarith
  · change z 2 = z 3
    have h := congrFun hu 2
    dsimp [u] at h
    linarith
  · rfl

end

end ResearchMain.DiagonalSchatten
