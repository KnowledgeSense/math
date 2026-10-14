import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyNonneg
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace ReciprocalQGamma

/-- Every nonnegative lower-bidiagonal matrix is totally nonnegative. -/
theorem bidiagonal_totallyNonneg {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hpos : ∀ i j, 0 ≤ A i j)
    (hsupport : ∀ i j, A i j ≠ 0 → j.val ≤ i.val ∧ i.val ≤ j.val + 1) :
    A.IsTotallyNonneg := by
  intro r rows cols hr hc
  rw [Matrix.det_apply']
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin r))]
  · simpa using Finset.prod_nonneg (fun i _ => hpos (rows i) (cols i))
  · intro σ _ hσ
    have hz : (∏ i : Fin r, A (rows (σ i)) (cols i)) = 0 := by
      by_contra hn
      have he : ∀ i : Fin r, A (rows (σ i)) (cols i) ≠ 0 :=
        fun i => (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ _)
      have hm : StrictMono σ := by
        intro i j hij
        by_contra h
        have hs : σ j < σ i := lt_of_le_of_ne (le_of_not_gt h)
          (fun hh => (ne_of_lt hij) (σ.injective hh.symm))
        have hrows : (rows (σ j)).val < (rows (σ i)).val := hr hs
        have hcols : (cols i).val < (cols j).val := hc hij
        have hi := hsupport (rows (σ i)) (cols i) (he i)
        have hj := hsupport (rows (σ j)) (cols j) (he j)
        omega
      apply hσ
      apply Equiv.ext
      exact congrFun hm.eq_id
    simp [Matrix.submatrix_apply, hz]
  · simp

def lowerBidiagonal (m j : ℕ) (c : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun a b => if a = b then 1 else if j < a.val ∧ b.val + 1 = a.val then c else 0

theorem lowerBidiagonal_totallyNonneg (m j : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (lowerBidiagonal m j c).IsTotallyNonneg := by
  apply bidiagonal_totallyNonneg
  · intro a b; unfold lowerBidiagonal; split_ifs <;> positivity
  · intro a b h
    unfold lowerBidiagonal at h
    split_ifs at h with hab hstep
    · subst b; omega
    · omega
    · contradiction

end ReciprocalQGamma
