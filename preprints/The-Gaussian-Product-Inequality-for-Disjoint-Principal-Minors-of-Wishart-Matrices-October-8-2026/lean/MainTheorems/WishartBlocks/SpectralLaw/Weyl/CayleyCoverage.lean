import MainTheorems.WishartBlocks.SpectralLaw.Weyl.SignFiber
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace ResearchMain.WishartBlocks.Weyl

open scoped BigOperators

theorem sum_det_add_signed_columns {n : ℕ}
    (A Q : Matrix (Fin n) (Fin n) ℝ) :
    (∑ s : Fin n → Bool, (A + Q * signMatrix s).det) = (2 : ℝ) ^ n * A.det := by
  classical
  have hprod (p : Equiv.Perm (Fin n)) :
      (∑ s : Fin n → Bool, ∏ i : Fin n,
        (A (p i) i + Q (p i) i * signValue (s i))) =
      (2 : ℝ) ^ n * ∏ i : Fin n, A (p i) i := by
    rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
      A (p i) i + Q (p i) i * signValue b)]
    have hsum (i : Fin n) :
        (∑ b : Bool, (A (p i) i + Q (p i) i * signValue b)) = 2 * A (p i) i := by
      simp [signValue]
      ring
    simp_rw [hsum]
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [Matrix.det_apply', Matrix.add_apply, signMatrix, Matrix.mul_diagonal,
    Function.comp_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hprod]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem exists_signed_columns_det_one_add_ne_zero {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    ∃ s : Fin n → Bool, (1 + Q * signMatrix s).det ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hs := sum_det_add_signed_columns (1 : Matrix (Fin n) (Fin n) ℝ) Q
  simp only [h, Finset.sum_const_zero, Matrix.det_one, mul_one] at hs
  exact (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)) hs.symm

end ResearchMain.WishartBlocks.Weyl
