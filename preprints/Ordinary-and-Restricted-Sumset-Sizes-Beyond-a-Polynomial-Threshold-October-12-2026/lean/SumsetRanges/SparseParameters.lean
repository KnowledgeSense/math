import SumsetRanges.StepUpperBound
import SumsetRanges.LargeParameters
import SumsetRanges.BinomialBounds

open Finset Polynomial
namespace SumsetRanges
open scoped BigOperators Classical

noncomputable def nonfreeSize (h : ℕ) (r u : ℕ → ℕ) : ℕ :=
  ∑ m ∈ Icc 2 h,(2*m*r m+m*u m)

noncomputable def sparsePolynomial (h c : ℕ) (r u : ℕ → ℕ) : Polynomial ℤ :=
  (1+X)^(c-nonfreeSize h r u) *
    ∏ m ∈ Icc 2 h, restrictedPolynomial (linearBlocks m (r m))*sharedBlockPolynomial m (u m)

theorem coeffNonneg_one_add_X : CoeffNonneg (1+X) :=
  coeffNonneg_add coeffNonneg_one (by simpa using coeffNonneg_X_pow 1)

theorem coeffNonneg_prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℤ)
    (hf : ∀ i∈s,CoeffNonneg (f i)) : CoeffNonneg (∏ i∈s,f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using coeffNonneg_one
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact coeffNonneg_mul (hf a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem coeffLE_prod {ι : Type*} (s : Finset ι) (f g : ι → Polynomial ℤ)
    (hf : ∀ i∈s,CoeffNonneg (f i)) (hg : ∀ i∈s,CoeffNonneg (g i))
    (hfg : ∀ i∈s,CoeffLE (f i) (g i)) : CoeffLE (∏ i∈s,f i) (∏ i∈s,g i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact coeffLE_refl _
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.prod_insert ha]
    apply coeffLE_mul (hf a (Finset.mem_insert_self _ _))
      (coeffNonneg_prod s g (fun i hi => hg i (Finset.mem_insert_of_mem hi)))
      (hfg a (Finset.mem_insert_self _ _))
    exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (fun i hi => hfg i (Finset.mem_insert_of_mem hi))

theorem restrictedPolynomial_le_binomial {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) : CoeffLE (restrictedPolynomial A) ((1+X)^A.card) := by
  intro q
  rw [coeff_restrictedPolynomial,coeff_one_add_X_pow]
  exact_mod_cast card_restrictedSums_le A q

theorem sharedBlockPolynomial_eq_restricted (m u : ℕ) (hm : 2≤m) :
    sharedBlockPolynomial m u=restrictedPolynomial (sharedAtomBlock m u) := by
  ext q
  rw [coeff_sharedBlockPolynomial m u q hm,coeff_restrictedPolynomial]

theorem sharedBlockPolynomial_nonneg (m u : ℕ) (hm : 2≤m) :
    CoeffNonneg (sharedBlockPolynomial m u) := by
  rw [sharedBlockPolynomial_eq_restricted m u hm]
  exact coeffNonneg_restrictedPolynomial _

theorem sparsePolynomial_nonneg (h c : ℕ) (r u : ℕ → ℕ) :
    CoeffNonneg (sparsePolynomial h c r u) := by
  apply coeffNonneg_mul (coeffNonneg_pow coeffNonneg_one_add_X _)
  apply coeffNonneg_prod
  intro m hm
  exact coeffNonneg_mul (coeffNonneg_restrictedPolynomial _)
    (sharedBlockPolynomial_nonneg m (u m) (Finset.mem_Icc.mp hm).1)

theorem nonfreeSize_step_r (h μ : ℕ) (r u : ℕ → ℕ) (hμ : μ∈Icc 2 h) :
    nonfreeSize h (Function.update r μ (r μ+1)) u=nonfreeSize h r u+2*μ := by
  calc
    _ = nonfreeSize h r u+∑ m∈Icc 2 h,if m=μ then 2*μ else 0 := by
      unfold nonfreeSize
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hm : m=μ
      · subst m; simp only [Function.update_self,ite_true]; ring
      · simp [hm]
    _ = _ := by simp [hμ]

theorem nonfreeSize_step_u (h μ : ℕ) (r u : ℕ → ℕ) (hμ : μ∈Icc 2 h) :
    nonfreeSize h r (Function.update u μ (u μ+1))=nonfreeSize h r u+μ := by
  calc
    _ = nonfreeSize h r u+∑ m∈Icc 2 h,if m=μ then μ else 0 := by
      unfold nonfreeSize
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hm : m=μ
      · subst m; simp only [Function.update_self,ite_true]; ring
      · simp [hm]
    _ = _ := by simp [hμ]

noncomputable def sparseOther (h : ℕ) (r u : ℕ → ℕ) (μ : ℕ) : Polynomial ℤ :=
  ∏ m∈(Icc 2 h).erase μ,restrictedPolynomial (linearBlocks m (r m))*sharedBlockPolynomial m (u m)

theorem sparsePolynomial_factor (h c μ : ℕ) (r u : ℕ → ℕ) (hμ : μ∈Icc 2 h) :
    sparsePolynomial h c r u=(1+X)^(c-nonfreeSize h r u)*
      (restrictedPolynomial (linearBlocks μ (r μ))*sharedBlockPolynomial μ (u μ))*sparseOther h r u μ := by
  unfold sparsePolynomial sparseOther
  rw [← Finset.mul_prod_erase _ _ hμ]
  ring

theorem sparseOther_update_r (h μ v : ℕ) (r u : ℕ → ℕ) :
    sparseOther h (Function.update r μ v) u μ=sparseOther h r u μ := by
  apply Finset.prod_congr rfl
  intro m hm
  rw [restrictedPolynomial_linearBlocks m _ (Finset.mem_Icc.mp (Finset.mem_erase.mp hm).2).1,
    restrictedPolynomial_linearBlocks m _ (Finset.mem_Icc.mp (Finset.mem_erase.mp hm).2).1]
  simp only [Function.update_of_ne (Finset.mem_erase.mp hm).1]

theorem sparseOther_update_u (h μ v : ℕ) (r u : ℕ → ℕ) :
    sparseOther h r (Function.update u μ v) μ=sparseOther h r u μ := by
  apply Finset.prod_congr rfl
  intro m hm
  simp only [Function.update_of_ne (Finset.mem_erase.mp hm).1]

/-- The exact sparse-polynomial change under an additional linear relation block. -/
theorem sparsePolynomial_step_r (h c μ : ℕ) (r u : ℕ → ℕ) (hμ : μ∈Icc 2 h)
    (hc : nonfreeSize h r u+2*μ≤c) :
    sparsePolynomial h c r u-sparsePolynomial h c (Function.update r μ (r μ+1)) u =
      X^μ*restrictedPolynomial (linearBlocks μ (r μ))*(1+X)^(c-nonfreeSize h r u-2*μ)*
        sharedBlockPolynomial μ (u μ)*sparseOther h r u μ := by
  rw [sparsePolynomial_factor h c μ r u hμ,
    sparsePolynomial_factor h c μ (Function.update r μ (r μ+1)) u hμ,
    nonfreeSize_step_r h μ r u hμ,sparseOther_update_r,Function.update_self]
  have he : c-nonfreeSize h r u=2*μ+(c-nonfreeSize h r u-2*μ) := by omega
  rw [he,pow_add]
  have hn : c-(nonfreeSize h r u+2*μ)=c-nonfreeSize h r u-2*μ := by omega
  rw [hn]
  simp only [Nat.add_sub_cancel_left]
  have hs := linearBlock_step μ (r μ) (Finset.mem_Icc.mp hμ).1
  linear_combination (1+X)^(c-nonfreeSize h r u-2*μ)*sharedBlockPolynomial μ (u μ)*sparseOther h r u μ*hs

/-- The exact sparse-polynomial change under an additional shared-atom relation. -/
theorem sparsePolynomial_step_u (h c μ : ℕ) (r u : ℕ → ℕ) (hμ : μ∈Icc 2 h)
    (hc : nonfreeSize h r u+μ≤c) :
    sparsePolynomial h c r u-sparsePolynomial h c r (Function.update u μ (u μ+1)) =
      ((1+X)^μ*sharedBlockPolynomial μ (u μ)-sharedBlockPolynomial μ (u μ+1))*
        (1+X)^(c-nonfreeSize h r u-μ)*restrictedPolynomial (linearBlocks μ (r μ))*sparseOther h r u μ := by
  rw [sparsePolynomial_factor h c μ r u hμ,
    sparsePolynomial_factor h c μ r (Function.update u μ (u μ+1)) hμ,
    nonfreeSize_step_u h μ r u hμ,sparseOther_update_u,Function.update_self]
  have he : c-nonfreeSize h r u=μ+(c-nonfreeSize h r u-μ) := by omega
  rw [he,pow_add]
  have hn : c-(nonfreeSize h r u+μ)=c-nonfreeSize h r u-μ := by omega
  rw [hn]
  simp only [Nat.add_sub_cancel_left]
  ring

end SumsetRanges
