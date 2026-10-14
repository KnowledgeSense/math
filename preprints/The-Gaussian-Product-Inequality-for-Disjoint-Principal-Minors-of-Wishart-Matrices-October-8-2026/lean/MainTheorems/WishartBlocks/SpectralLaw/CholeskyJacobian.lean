import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

open scoped BigOperators

abbrev LowerIndex (n : ℕ) := {e : Fin n ×ₗ Fin n // e.2 ≤ e.1}

def choleskyJacobian {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (LowerIndex n) (LowerIndex n) ℝ := fun e f =>
  (if e.val.1 = f.val.1 then L e.val.2 f.val.2 else 0) +
    (if e.val.2 = f.val.1 then L e.val.1 f.val.2 else 0)

theorem choleskyJacobian_lowerTriangular {n : ℕ}
    {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular) :
    (choleskyJacobian L).IsLowerTriangular := by
  intro e f hef
  change e < f at hef
  have hlex := (Prod.Lex.lt_iff).mp hef
  unfold choleskyJacobian
  rcases hlex with hrow | ⟨hrow, hcol⟩
  · change e.val.1 < f.val.1 at hrow
    have h₁ : e.val.1 ≠ f.val.1 := ne_of_lt hrow
    have h₂ : e.val.2 ≠ f.val.1 := ne_of_lt (e.property.trans_lt hrow)
    simp only [h₁, h₂, ite_false, zero_add]
  · change e.val.1 = f.val.1 at hrow
    change e.val.2 < f.val.2 at hcol
    have hzero : L e.val.2 f.val.2 = 0 := hL hcol
    have h₂ : e.val.2 ≠ f.val.1 := by
      intro heq
      have := f.property
      rw [← heq] at this
      exact (not_le_of_gt hcol) this
    simp only [hrow, hzero, h₂, ite_true, ite_false, add_zero]

theorem choleskyJacobian_diagonal {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℝ) (e : LowerIndex n) :
    choleskyJacobian L e e =
      if e.val.1 = e.val.2 then 2 * L e.val.2 e.val.2 else L e.val.2 e.val.2 := by
  unfold choleskyJacobian
  by_cases he : e.val.1 = e.val.2
  · simp only [he, ite_true]
    ring
  · simp only [ite_true, Ne.symm he, he, ite_false, add_zero]

theorem choleskyJacobian_det {n : ℕ}
    {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular) :
    (choleskyJacobian L).det =
      ∏ e : LowerIndex n,
        if e.val.1 = e.val.2 then 2 * L e.val.2 e.val.2 else L e.val.2 e.val.2 := by
  rw [Matrix.det_of_isLowerTriangular _ (choleskyJacobian_lowerTriangular hL)]
  exact Finset.prod_congr rfl fun e _ => choleskyJacobian_diagonal L e

theorem choleskyJacobian_det_pos {n : ℕ}
    {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular)
    (hdiag : ∀ i, 0 < L i i) : 0 < (choleskyJacobian L).det := by
  rw [choleskyJacobian_det hL]
  apply Finset.prod_pos
  intro e _
  split_ifs
  · exact mul_pos (by norm_num) (hdiag _)
  · exact hdiag _

end ResearchMain.WishartBlocks
