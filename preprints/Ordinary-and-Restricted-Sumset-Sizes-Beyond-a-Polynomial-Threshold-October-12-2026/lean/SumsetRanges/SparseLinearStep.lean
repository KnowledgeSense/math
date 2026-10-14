import SumsetRanges.SparseBounds

open Finset Polynomial
namespace SumsetRanges
open scoped BigOperators Classical

noncomputable def sparseCore (h : ℕ) (r u : ℕ → ℕ) : Polynomial ℤ :=
  ∏ m∈Icc 2 h,restrictedPolynomial (linearBlocks m (r m))*sharedBlockPolynomial m (u m)

theorem sparseCore_nonneg (h : ℕ) (r u : ℕ → ℕ) : CoeffNonneg (sparseCore h r u) := by
  apply coeffNonneg_prod
  intro m hm
  exact coeffNonneg_mul (coeffNonneg_restrictedPolynomial _)
    (sharedBlockPolynomial_nonneg m (u m) (Finset.mem_Icc.mp hm).1)

@[simp] theorem sparseCore_constant (h : ℕ) (r u : ℕ → ℕ) : (sparseCore h r u).coeff 0=1 := by
  unfold sparseCore
  rw [coeff_zero_prod]
  apply Finset.prod_eq_one
  intro m hm
  rw [Polynomial.mul_coeff_zero,restrictedPolynomial_constant,
    sharedBlockPolynomial_constant m (u m) (Finset.mem_Icc.mp hm).1]
  norm_num

theorem sparseCore_le_binomial (h : ℕ) (r u : ℕ → ℕ) :
    CoeffLE (sparseCore h r u) ((1+X)^(nonfreeSize h r u)) := by
  unfold nonfreeSize
  rw [← Finset.prod_pow_eq_pow_sum]
  apply coeffLE_prod
  · intro m hm
    exact coeffNonneg_mul (coeffNonneg_restrictedPolynomial _)
      (sharedBlockPolynomial_nonneg m (u m) (Finset.mem_Icc.mp hm).1)
  · intro m _; exact coeffNonneg_pow coeffNonneg_one_add_X _
  · intro m hm; exact sparse_block_le_binomial m r u (Finset.mem_Icc.mp hm).1

noncomputable def linearStepRemainder (h c μ : ℕ) (r u : ℕ → ℕ) : Polynomial ℤ :=
  (1+X)^(c-nonfreeSize h r u-2*μ)*sparseCore h r u

theorem sparse_linear_step_factored (h c μ : ℕ) (r u : ℕ → ℕ) (hμ : μ∈Icc 2 h)
    (hc : nonfreeSize h r u+2*μ≤c) :
    sparsePolynomial h c r u-sparsePolynomial h c (Function.update r μ (r μ+1)) u =
      X^μ*linearStepRemainder h c μ r u := by
  rw [sparsePolynomial_step_r h c μ r u hμ hc]
  unfold linearStepRemainder sparseCore
  rw [← Finset.mul_prod_erase _ _ hμ]
  change _=X^μ*((1+X)^(c-nonfreeSize h r u-2*μ)*
    ((restrictedPolynomial (linearBlocks μ (r μ))*sharedBlockPolynomial μ (u μ))*sparseOther h r u μ))
  ring

theorem linearStepRemainder_lower (h c μ : ℕ) (r u : ℕ → ℕ) :
    CoeffLE ((1+X)^(c-nonfreeSize h r u-2*μ)) (linearStepRemainder h c μ r u) := by
  have hh := coeffLE_mul (coeffNonneg_pow coeffNonneg_one_add_X (c-nonfreeSize h r u-2*μ))
    (sparseCore_nonneg h r u) (coeffLE_refl _)
    (one_coeffLE_of_constant (sparseCore_nonneg h r u) (sparseCore_constant h r u))
  simpa only [mul_one,linearStepRemainder] using hh

theorem linearStepRemainder_upper (h c μ : ℕ) (r u : ℕ → ℕ)
    (hc : nonfreeSize h r u+2*μ≤c) :
    CoeffLE (linearStepRemainder h c μ r u) ((1+X)^(c-2*μ)) := by
  have hh := coeffLE_mul (coeffNonneg_pow coeffNonneg_one_add_X (c-nonfreeSize h r u-2*μ))
    (coeffNonneg_pow coeffNonneg_one_add_X (nonfreeSize h r u)) (coeffLE_refl _)
    (sparseCore_le_binomial h r u)
  rw [← pow_add,show c-nonfreeSize h r u-2*μ+nonfreeSize h r u=c-2*μ by omega] at hh
  exact hh

theorem linearStepRemainder_nonneg (h c μ : ℕ) (r u : ℕ → ℕ) :
    CoeffNonneg (linearStepRemainder h c μ r u) :=
  coeffNonneg_mul (coeffNonneg_pow coeffNonneg_one_add_X _) (sparseCore_nonneg h r u)

@[simp] theorem linearStepRemainder_constant (h c μ : ℕ) (r u : ℕ → ℕ) :
    (linearStepRemainder h c μ r u).coeff 0=1 := by
  simp [linearStepRemainder,Polynomial.mul_coeff_zero,coeff_one_add_X_pow]

end SumsetRanges
