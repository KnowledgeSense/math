import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators

theorem weighted_cauchy_schwarz {J : Type*} [Fintype J]
    (w x y : J → ℝ) (hw : ∀ j, 0 < w j) :
    (∑ j, x j * y j) ^ 2 ≤ (∑ j, w j * x j ^ 2) * (∑ j, y j ^ 2 / w j) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro j _
    exact mul_nonneg (hw j).le (sq_nonneg _)
  · intro j _
    exact div_nonneg (sq_nonneg _) (hw j).le
  · intro j _
    apply le_of_eq
    field_simp [(hw j).ne']

theorem positive_dual_bound {S A R : ℝ} (hS : 0 ≤ S) (hR : 0 ≤ R)
    (hA : A ≤ 2 * S) (hCS : (2 * S) ^ 2 ≤ A * R) : S ≤ R / 2 := by
  by_cases hSz : S = 0
  · rw [hSz]
    positivity
  · have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hSz)
    have hm : A * R ≤ (2 * S) * R := mul_le_mul_of_nonneg_right hA hR
    nlinarith

theorem negative_dual_bound {S A R : ℝ} (hS : S ≤ 0) (hR : R ≤ 0)
    (hA : A ≤ -2 * S) (hCS : (2 * S) ^ 2 ≤ A * (-R)) : R / 2 ≤ S := by
  have h := positive_dual_bound (S := -S) (A := A) (R := -R)
    (neg_nonneg.mpr hS) (neg_nonneg.mpr hR) (by linarith) (by nlinarith)
  linarith

end

end ResearchMain.DiagonalSchatten
