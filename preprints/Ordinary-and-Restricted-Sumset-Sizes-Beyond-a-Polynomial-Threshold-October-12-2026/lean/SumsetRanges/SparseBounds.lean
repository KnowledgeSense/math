import SumsetRanges.SparseParameters
import Mathlib.Algebra.Polynomial.BigOperators

open Finset Polynomial
namespace SumsetRanges
open scoped BigOperators Classical

@[simp] theorem restrictedPolynomial_constant {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) : (restrictedPolynomial A).coeff 0=1 := by
  simp [coeff_restrictedPolynomial]

@[simp] theorem sharedBlockPolynomial_constant (m u : ℕ) (hm : 2≤m) :
    (sharedBlockPolynomial m u).coeff 0=1 := by
  rw [sharedBlockPolynomial_eq_restricted m u hm]
  simp

theorem one_coeffLE_of_constant {P : Polynomial ℤ} (hP : CoeffNonneg P) (h0 : P.coeff 0=1) :
    CoeffLE 1 P := by
  intro q
  by_cases hq : q=0
  · subst q; simp [h0]
  · simpa only [Polynomial.coeff_one, ite_eq_right hq] using hP q

theorem sparseOther_nonneg (h μ : ℕ) (r u : ℕ → ℕ) : CoeffNonneg (sparseOther h r u μ) := by
  apply coeffNonneg_prod
  intro m hm
  exact coeffNonneg_mul (coeffNonneg_restrictedPolynomial _)
    (sharedBlockPolynomial_nonneg m (u m) (Finset.mem_Icc.mp (Finset.mem_erase.mp hm).2).1)

@[simp] theorem sparseOther_constant (h μ : ℕ) (r u : ℕ → ℕ) :
    (sparseOther h r u μ).coeff 0=1 := by
  unfold sparseOther
  rw [coeff_zero_prod]
  apply Finset.prod_eq_one
  intro m hm
  rw [Polynomial.mul_coeff_zero,restrictedPolynomial_constant,
    sharedBlockPolynomial_constant m (u m) (Finset.mem_Icc.mp (Finset.mem_erase.mp hm).2).1]
  norm_num

theorem sparse_block_le_binomial (m : ℕ) (r u : ℕ → ℕ) (hm : 2≤m) :
    CoeffLE (restrictedPolynomial (linearBlocks m (r m))*sharedBlockPolynomial m (u m))
      ((1+X)^(2*m*r m+m*u m)) := by
  rw [pow_add]
  apply coeffLE_mul (coeffNonneg_restrictedPolynomial _) (coeffNonneg_pow coeffNonneg_one_add_X _)
  · simpa only [card_linearBlocks m (r m) hm] using restrictedPolynomial_le_binomial (linearBlocks m (r m))
  · rw [sharedBlockPolynomial_eq_restricted m (u m) hm]
    simpa only [card_sharedAtomBlock m (u m) hm] using restrictedPolynomial_le_binomial (sharedAtomBlock m (u m))

theorem sparseOther_le_binomial (h μ : ℕ) (r u : ℕ → ℕ) :
    CoeffLE (sparseOther h r u μ)
      ((1+X)^(∑ m∈(Icc 2 h).erase μ,(2*m*r m+m*u m))) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  apply coeffLE_prod
  · intro m hm
    exact coeffNonneg_mul (coeffNonneg_restrictedPolynomial _)
      (sharedBlockPolynomial_nonneg m (u m) (Finset.mem_Icc.mp (Finset.mem_erase.mp hm).2).1)
  · intro m _
    exact coeffNonneg_pow coeffNonneg_one_add_X _
  · intro m hm
    exact sparse_block_le_binomial m r u (Finset.mem_Icc.mp (Finset.mem_erase.mp hm).2).1

theorem sparsePolynomial_le_binomial (h c : ℕ) (r u : ℕ → ℕ) (hc : nonfreeSize h r u≤c) :
    CoeffLE (sparsePolynomial h c r u) ((1+X)^c) := by
  have he : c=(c-nonfreeSize h r u)+nonfreeSize h r u := by omega
  conv_rhs => rw [he,pow_add]
  apply coeffLE_mul (coeffNonneg_pow coeffNonneg_one_add_X _)
    (coeffNonneg_pow coeffNonneg_one_add_X _) (coeffLE_refl _)
  unfold nonfreeSize
  rw [← Finset.prod_pow_eq_pow_sum]
  apply coeffLE_prod
  · intro m hm
    exact coeffNonneg_mul (coeffNonneg_restrictedPolynomial _)
      (sharedBlockPolynomial_nonneg m (u m) (Finset.mem_Icc.mp hm).1)
  · intro m _
    exact coeffNonneg_pow coeffNonneg_one_add_X _
  · intro m hm
    exact sparse_block_le_binomial m r u (Finset.mem_Icc.mp hm).1

end SumsetRanges
