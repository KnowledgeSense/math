import SumsetRanges.TaggedConvolution
import SumsetRanges.SharedBlockSeries

open Finset Polynomial
namespace SumsetRanges

noncomputable def restrictedPolynomial {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) : Polynomial ℤ :=
  ∑ q ∈ range (A.card+1), monomial q ((restrictedSums A q).card : ℤ)

theorem coeff_restrictedPolynomial {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) (q : ℕ) :
    (restrictedPolynomial A).coeff q = ((restrictedSums A q).card : ℤ) := by
  classical
  simp only [restrictedPolynomial,finsetSum_coeff,coeff_monomial]
  by_cases hq : q∈range (A.card+1)
  · simp [hq]
  · have hlt : A.card<q := by have := mem_range.not.mp hq; omega
    have hz := card_restrictedSums_le A q
    rw [Nat.choose_eq_zero_of_lt hlt] at hz
    have hc : (restrictedSums A q).card=0 := by omega
    simp [hq,hc]

theorem restrictedPolynomial_taggedUnion {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
    [DecidableEq α] [DecidableEq β] (A : Finset α) (B : Finset β) :
    restrictedPolynomial (taggedUnion A B) = restrictedPolynomial A * restrictedPolynomial B := by
  ext q
  rw [coeff_restrictedPolynomial,card_restrictedSums_taggedUnion,coeff_mul]
  simp only [coeff_restrictedPolynomial]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun p r => ((restrictedSums A p).card : ℤ) * ((restrictedSums B r).card : ℤ)) q]
  push_cast
  rfl

theorem restrictedPolynomial_sharedAtomBlock (m u : ℕ) (hm : 2 ≤ m) :
    restrictedPolynomial (sharedAtomBlock m u) = ∑ j ∈ range (u+1),
      (u.choose j : Polynomial ℤ) * ((1+X)^m-X-X^(m-1))^(u-j) * ambiguityPolynomial m j := by
  rw [← sharedBlockPolynomial_formula m u hm]
  ext q
  rw [coeff_restrictedPolynomial,coeff_sharedBlockPolynomial m u q hm]

end SumsetRanges
