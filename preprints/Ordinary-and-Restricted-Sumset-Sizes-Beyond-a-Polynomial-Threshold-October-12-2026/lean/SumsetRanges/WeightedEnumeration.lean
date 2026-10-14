import SumsetRanges.SharedNormalForms
import Mathlib.Algebra.Polynomial.Coeff

open Finset Polynomial
namespace SumsetRanges

/-- Finite generating polynomial of the degrees of actual normal forms. -/
noncomputable def weightPolynomial {α : Type*} [Fintype α] (w : α → ℕ) : Polynomial ℤ :=
  ∑ a, X^(w a)

theorem coeff_weightPolynomial {α : Type*} [Fintype α] (w : α → ℕ) (q : ℕ) :
    (weightPolynomial w).coeff q = ((Finset.univ.filter (fun a => w a=q)).card : ℤ) := by
  classical
  simp only [weightPolynomial, finsetSum_coeff, coeff_X_pow]
  rw [← Finset.sum_filter]
  simp [eq_comm]

theorem weightPolynomial_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (w : β → ℕ) : weightPolynomial (w ∘ e) = weightPolynomial w := by
  unfold weightPolynomial
  exact e.sum_comp (fun b => (X : Polynomial ℤ)^w b)

theorem weightPolynomial_prod {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℕ) (v : β → ℕ) :
    weightPolynomial (fun x : α × β => w x.1+v x.2) = weightPolynomial w * weightPolynomial v := by
  simp only [weightPolynomial, Fintype.sum_prod_type, pow_add, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem weightPolynomial_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (w : ∀ i, κ i → ℕ) :
    weightPolynomial (fun x : ∀ i, κ i => ∑ i, w i (x i)) = ∏ i, weightPolynomial (w i) := by
  unfold weightPolynomial
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact (Finset.prod_pow_eq_pow_sum _ _ _).symm

noncomputable def rowPolynomial (m : ℕ) : Polynomial ℤ :=
  weightPolynomial (fun S : {S : Finset (RowIndex m) // S≠rowAlpha m ∧ S≠rowBeta m} => S.val.card)

theorem coeff_rowPolynomial (m q : ℕ) :
    (rowPolynomial m).coeff q = ((unambiguousRows m q).card : ℤ) := by
  classical
  rw [rowPolynomial, coeff_weightPolynomial]
  congr 1
  apply Finset.card_bij (fun S _ => S.val)
  · intro S hS
    have hq := (Finset.mem_filter.mp hS).2
    simp only [unambiguousRows, Finset.mem_erase, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    exact ⟨S.property.2,S.property.1,hq⟩
  · intro S _ T _ he
    exact Subtype.ext he
  · intro S hS
    simp only [unambiguousRows, Finset.mem_erase, Finset.mem_powersetCard,
      Finset.subset_univ, true_and] at hS
    refine ⟨⟨S,hS.2.1,hS.1⟩,?_,rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hS.2.2

theorem rowPolynomial_eq (m : ℕ) (hm : 2 ≤ m) :
    rowPolynomial m = (1+X)^m-X-X^(m-1) := by
  ext q
  rw [coeff_rowPolynomial, card_unambiguousRows m q hm]
  simp only [coeff_sub, coeff_one_add_X_pow, coeff_X, coeff_X_pow]
  have hchoose : m.choose (m-1)=m := by
    rw [Nat.choose_symm (by omega : 1≤m),Nat.choose_one_right]
  by_cases hq : q=1 <;> by_cases hq' : q=m-1
  · have hm2 : m=2 := by omega
    subst m
    subst q
    norm_num
  · subst q
    simp_all only [Nat.choose_one_right, ite_true, ite_false, Nat.sub_zero, sub_zero]
    omega
  · simp_all only [ite_true, ite_false, Nat.sub_zero]
    omega
  · simp only [ite_eq_right hq, ite_eq_right hq', ite_eq_right (Ne.symm hq),
      Nat.sub_zero, sub_zero]


/-- The actual shared-atom block polynomial is enumerated by its proved normal forms. -/
noncomputable def sharedBlockPolynomial (m u : ℕ) : Polynomial ℤ :=
  weightPolynomial (normalDegree (m := m) (u := u))

theorem coeff_sharedBlockPolynomial (m u q : ℕ) (hm : 2 ≤ m) :
    (sharedBlockPolynomial m u).coeff q = ((restrictedSums (sharedAtomBlock m u) q).card : ℤ) := by
  rw [sharedBlockPolynomial, coeff_weightPolynomial, card_sharedAtomBlock_normal_forms m u q hm]

end SumsetRanges
