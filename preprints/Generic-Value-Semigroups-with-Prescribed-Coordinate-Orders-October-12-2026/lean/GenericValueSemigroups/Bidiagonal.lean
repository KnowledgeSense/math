import GenericValueSemigroups.CauchyBinet
import Mathlib.Order.Preorder.Finite

namespace GenericValueSemigroups
open Matrix Finset

/-- An ordered minor of a lower bidiagonal matrix is its diagonal product. -/
theorem det_submatrix_lower_bidiagonal {N q : ℕ} (B : Matrix (Fin N) (Fin N) ℝ)
    (hband : ∀ i j, B i j ≠ 0 → j.val ≤ i.val ∧ i.val ≤ j.val + 1)
    (rows cols : Fin q → Fin N) (hr : StrictMono rows) (hc : StrictMono cols) :
    (B.submatrix rows cols).det = ∏ i, B (rows i) (cols i) := by
  classical
  have hterm (σ : Equiv.Perm (Fin q)) (hne : σ ≠ 1) :
      ∏ i, B (rows (σ i)) (cols i) = 0 := by
    by_contra hn
    have hentry (i : Fin q) : B (rows (σ i)) (cols i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)
    have hmono : StrictMono σ := by
      intro i j hij
      by_contra h
      have hrev : σ j < σ i := lt_of_le_of_ne (le_of_not_gt h) (by
        intro he; exact (ne_of_lt hij) (σ.injective he.symm))
      have hrow := hr hrev
      have hcol := hc hij
      have hi := hband _ _ (hentry i)
      have hj := hband _ _ (hentry j)
      have hrow' : (rows (σ j)).val < (rows (σ i)).val := hrow
      have hcol' : (cols i).val < (cols j).val := hcol
      omega
    have he : (σ : Fin q → Fin q) = id := hmono.eq_id
    apply hne
    exact Equiv.ext (congrFun he)
  rw [Matrix.det_apply']
  have heq : (∑ σ : Equiv.Perm (Fin q),
      (Equiv.Perm.sign σ : ℝ) * ∏ i, B (rows (σ i)) (cols i)) =
      ∏ i, B (rows i) (cols i) := by
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin q))]
    · simp
    · intro σ _ hσ; simp [hterm σ hσ]
    · simp
  exact heq

/-- Every lower bidiagonal matrix with nonnegative entries is totally nonnegative. -/
theorem totallyNonneg_of_lower_bidiagonal {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ)
    (hpos : ∀ i j, 0 ≤ B i j)
    (hband : ∀ i j, B i j ≠ 0 → j.val ≤ i.val ∧ i.val ≤ j.val + 1) :
    B.IsTotallyNonneg := by
  intro q rows cols hr hc
  rw [det_submatrix_lower_bidiagonal B hband rows cols hr hc]
  exact Finset.prod_nonneg (fun i _ => hpos _ _)

end GenericValueSemigroups
