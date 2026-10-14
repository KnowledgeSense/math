import SumsetRanges.SparseLinearStep

open Finset Polynomial
namespace SumsetRanges
open scoped BigOperators Classical

noncomputable def sharedStepQuotient (m u : ℕ) : Polynomial ℤ :=
  ∑ j∈range u,(u.choose (j+1) : Polynomial ℤ)*(rowPolynomial m)^(u-1-j)*ambiguityPolynomial m j

theorem sharedStepQuotient_factor (m u : ℕ) (hm : 2≤m) :
    (1+X)^m*sharedBlockPolynomial m u-sharedBlockPolynomial m (u+1)=X^m*sharedStepQuotient m u :=
  sharedBlock_step_factored m u hm

theorem coeffLE_cancel_X {P Q : Polynomial ℤ} (m : ℕ) (h : CoeffLE (X^m*P) (X^m*Q)) :
    CoeffLE P Q := by
  intro d
  simpa only [coeff_X_pow_mul] using h (d+m)

theorem sharedStepQuotient_nonneg (m u : ℕ) (hm : 2≤m) :
    CoeffNonneg (sharedStepQuotient m u) := by
  intro d
  have hh := sharedBlock_step_nonneg m u hm (d+m)
  rwa [sharedStepQuotient_factor m u hm,coeff_X_pow_mul] at hh

theorem sharedStepQuotient_lower (m u : ℕ) (hm : 2≤m) (hu : 1≤u) :
    CoeffLE ((u : Polynomial ℤ)*(rowPolynomial m)^(u-1)) (sharedStepQuotient m u) := by
  apply coeffLE_cancel_X m
  have hh := sharedBlock_step_lower m u hm hu
  rw [sharedStepQuotient_factor m u hm] at hh
  convert hh using 1; ring

theorem sharedStepQuotient_upper (m u : ℕ) (hm : 2≤m) (hu : 1≤u) :
    CoeffLE (sharedStepQuotient m u) ((u : Polynomial ℤ)*(1+X)^(m*(u-1))) := by
  apply coeffLE_cancel_X m
  have hh := sharedBlock_step_upper m u hm hu
  rw [sharedStepQuotient_factor m u hm] at hh
  convert hh using 1; ring

noncomputable def sharedStepRemainder (h c μ : ℕ) (r u : ℕ → ℕ) : Polynomial ℤ :=
  sharedStepQuotient μ (u μ)*(1+X)^(c-nonfreeSize h r u-μ)*
    restrictedPolynomial (linearBlocks μ (r μ))*sparseOther h r u μ

theorem sparse_shared_step_factored (h c μ : ℕ) (r u : ℕ → ℕ) (hμ : μ∈Icc 2 h)
    (hc : nonfreeSize h r u+μ≤c) :
    sparsePolynomial h c r u-sparsePolynomial h c r (Function.update u μ (u μ+1)) =
      X^μ*sharedStepRemainder h c μ r u := by
  rw [sparsePolynomial_step_u h c μ r u hμ hc,
    sharedStepQuotient_factor μ (u μ) (Finset.mem_Icc.mp hμ).1]
  unfold sharedStepRemainder
  ring

theorem sharedStepRemainder_nonneg (h c μ : ℕ) (r u : ℕ → ℕ) (hμ : 2≤μ) :
    CoeffNonneg (sharedStepRemainder h c μ r u) :=
  coeffNonneg_mul (coeffNonneg_mul (coeffNonneg_mul
    (sharedStepQuotient_nonneg μ (u μ) hμ) (coeffNonneg_pow coeffNonneg_one_add_X _))
    (coeffNonneg_restrictedPolynomial _)) (sparseOther_nonneg h μ r u)

@[simp] theorem rowPolynomial_constant (m : ℕ) (hm : 2≤m) : (rowPolynomial m).coeff 0=1 := by
  rw [rowPolynomial_eq m hm]
  simp [coeff_sub,coeff_one_add_X_pow,show ¬(0=m-1) by omega]

theorem sharedStepQuotient_lower_constant (m u : ℕ) (hm : 2≤m) (hu : 1≤u) :
    CoeffLE (u : Polynomial ℤ) (sharedStepQuotient m u) := by
  have hpall : ∀ v,((rowPolynomial m)^v).coeff 0=1 := by
    intro v
    induction v with
    | zero => simp
    | succ v ih => rw [pow_succ,Polynomial.mul_coeff_zero,ih,rowPolynomial_constant m hm]; norm_num
  have hp := hpall (u-1)
  have hh := coeffLE_mul (coeffNonneg_natCast u)
    (coeffNonneg_pow (coeffNonneg_rowPolynomial m) (u-1)) (coeffLE_refl _)
    (one_coeffLE_of_constant (coeffNonneg_pow (coeffNonneg_rowPolynomial m) (u-1)) hp)
  rw [mul_one] at hh
  intro d
  exact (hh d).trans (sharedStepQuotient_lower m u hm hu d)

theorem sharedStepRemainder_lower (h c μ : ℕ) (r u : ℕ → ℕ) (hμ : 2≤μ) (hu : 1≤u μ) :
    CoeffLE ((u μ : Polynomial ℤ)*(1+X)^(c-nonfreeSize h r u-μ))
      (sharedStepRemainder h c μ r u) := by
  have h1 := coeffLE_mul (coeffNonneg_natCast (u μ)) (coeffNonneg_pow coeffNonneg_one_add_X
    (c-nonfreeSize h r u-μ)) (sharedStepQuotient_lower_constant μ (u μ) hμ hu) (coeffLE_refl _)
  have h2 := coeffLE_mul (coeffNonneg_mul (coeffNonneg_natCast (u μ))
    (coeffNonneg_pow coeffNonneg_one_add_X (c-nonfreeSize h r u-μ)))
    (coeffNonneg_restrictedPolynomial (linearBlocks μ (r μ))) h1
    (one_coeffLE_of_constant (coeffNonneg_restrictedPolynomial _) (restrictedPolynomial_constant _))
  rw [mul_one] at h2
  have h3 := coeffLE_mul (coeffNonneg_mul (coeffNonneg_natCast (u μ))
    (coeffNonneg_pow coeffNonneg_one_add_X (c-nonfreeSize h r u-μ)))
    (sparseOther_nonneg h μ r u) h2
    (one_coeffLE_of_constant (sparseOther_nonneg h μ r u) (sparseOther_constant h μ r u))
  simpa only [mul_one,sharedStepRemainder] using h3

theorem sharedStepRemainder_upper (h c μ : ℕ) (r u : ℕ → ℕ) (hμ : μ∈Icc 2 h)
    (hu : 1≤u μ) (hc : nonfreeSize h r u+μ≤c) :
    CoeffLE (sharedStepRemainder h c μ r u) ((u μ : Polynomial ℤ)*(1+X)^(c-2*μ)) := by
  have hμ2 := (Finset.mem_Icc.mp hμ).1
  let n := c-nonfreeSize h r u-μ
  let o := ∑ m∈(Icc 2 h).erase μ,(2*m*r m+m*u m)
  have hν : nonfreeSize h r u=2*μ*r μ+μ*u μ+o := by
    unfold nonfreeSize
    exact (Finset.add_sum_erase _ _ hμ).symm
  have hu' : μ*(u μ-1)+μ=μ*u μ := by
    calc
      _=μ*((u μ-1)+1) := by ring
      _=_ := by rw [Nat.sub_add_cancel hu]
  have h1 := coeffLE_mul (sharedStepQuotient_nonneg μ (u μ) hμ2)
    (coeffNonneg_pow coeffNonneg_one_add_X n)
    (sharedStepQuotient_upper μ (u μ) hμ2 hu) (coeffLE_refl ((1+X)^n))
  have hg : CoeffLE (restrictedPolynomial (linearBlocks μ (r μ))) ((1+X)^(2*μ*r μ)) := by
    simpa only [card_linearBlocks μ (r μ) hμ2] using restrictedPolynomial_le_binomial (linearBlocks μ (r μ))
  have h2 := coeffLE_mul (coeffNonneg_mul (sharedStepQuotient_nonneg μ (u μ) hμ2)
    (coeffNonneg_pow coeffNonneg_one_add_X n)) (coeffNonneg_pow coeffNonneg_one_add_X (2*μ*r μ)) h1 hg
  have h3 := coeffLE_mul (coeffNonneg_mul
    (coeffNonneg_mul (sharedStepQuotient_nonneg μ (u μ) hμ2) (coeffNonneg_pow coeffNonneg_one_add_X n))
    (coeffNonneg_restrictedPolynomial (linearBlocks μ (r μ))))
    (coeffNonneg_pow coeffNonneg_one_add_X o) h2 (sparseOther_le_binomial h μ r u)
  have he : (u μ : Polynomial ℤ)*(1+X)^(μ*(u μ-1))*(1+X)^n*(1+X)^(2*μ*r μ)*(1+X)^o =
      (u μ : Polynomial ℤ)*(1+X)^(c-2*μ) := by
    rw [mul_assoc,← pow_add,mul_assoc,← pow_add,mul_assoc,← pow_add]
    congr 2
    dsimp [n]
    omega
  rw [he] at h3
  exact h3

end SumsetRanges
