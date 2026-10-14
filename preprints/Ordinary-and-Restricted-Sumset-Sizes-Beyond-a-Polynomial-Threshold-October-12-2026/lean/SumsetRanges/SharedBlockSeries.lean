import SumsetRanges.BackgroundRows
import Mathlib.Algebra.BigOperators.Intervals

open Finset Polynomial
namespace SumsetRanges

noncomputable def ambiguityPolynomial (m j : ℕ) : Polynomial ℤ :=
  ∑ l ∈ range (j+1), X^(j+l*(m-2))

theorem ambiguityPolynomial_parameter (m j : ℕ) (hm : 2 ≤ m) :
    (∑ p : Fin (j+1), (X : Polynomial ℤ)^(p.val+(j-p.val)*(m-1))) =
      ambiguityPolynomial m j := by
  rw [Fin.sum_univ_eq_sum_range (fun p => (X : Polynomial ℤ)^(p+(j-p)*(m-1))) (j+1)]
  unfold ambiguityPolynomial
  rw [← Finset.sum_range_reflect (fun l => (X : Polynomial ℤ)^(j+l*(m-2))) (j+1)]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  have hpj : p≤j := Nat.le_of_lt_succ (mem_range.mp hp)
  have he : j+1-1-p = j-p := by omega
  rw [he]
  have hm' : m-1=(m-2)+1 := by omega
  rw [hm']
  have hs := Nat.sub_add_cancel hpj
  nlinarith

theorem sharedBlockPolynomial_by_ambiguous_set (m u : ℕ) (hm : 2 ≤ m) :
    sharedBlockPolynomial m u =
      ∑ J : Finset (Fin u), (rowPolynomial m)^(u-J.card) * ambiguityPolynomial m J.card := by
  classical
  unfold sharedBlockPolynomial weightPolynomial
  simp only [SharedNormalData, Fintype.sum_sigma, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro J _
  have hd (R : {R : Fin u → Finset (RowIndex m) // ValidRows J R}) (p : Fin (J.card+1)) :
      normalDegree (⟨J,R,p⟩ : SharedNormalData m u) = p.val+(J.card-p.val)*(m-1) +
        ∑ i ∈ Finset.univ.filter (fun i => i ∉ J), (R.val i).card := by
    exact card_canonicalRows J R.val p.val (by omega)
  have hfac (R : {R : Fin u → Finset (RowIndex m) // ValidRows J R}) :
      (∑ p : Fin (J.card+1), (X : Polynomial ℤ)^normalDegree (⟨J,R,p⟩ : SharedNormalData m u)) =
        (∑ p : Fin (J.card+1), (X : Polynomial ℤ)^(p.val+(J.card-p.val)*(m-1))) *
        X^(∑ i ∈ Finset.univ.filter (fun i => i ∉ J), (R.val i).card) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [hd, pow_add]
  simp_rw [hfac]
  rw [← Finset.mul_sum]
  have he : (∑ R : {R : Fin u → Finset (RowIndex m) // ValidRows J R},
      (X : Polynomial ℤ)^(∑ i ∈ Finset.univ.filter (fun i => i ∉ J), (R.val i).card)) =
      (rowPolynomial m)^(u-J.card) := background_weightPolynomial m u J
  rw [he, ambiguityPolynomial_parameter m J.card hm]
  ring

theorem sum_finsets_by_card (u : ℕ) (f : ℕ → Polynomial ℤ) :
    (∑ J : Finset (Fin u), f J.card) = ∑ j ∈ range (u+1), (u.choose j : Polynomial ℤ)*f j := by
  classical
  have ht : ∀ J ∈ (Finset.univ : Finset (Finset (Fin u))), J.card ∈ range (u+1) := by
    intro J _
    apply mem_range.mpr
    have hh := Finset.card_le_card (Finset.subset_univ J)
    simp only [Finset.card_univ, Fintype.card_fin] at hh
    omega
  rw [← Finset.sum_fiberwise_of_maps_to' ht f]
  apply Finset.sum_congr rfl
  intro j _
  have hf : (Finset.univ.filter (fun J : Finset (Fin u) => J.card=j)) =
      (Finset.univ : Finset (Fin u)).powersetCard j := by
    ext J
    simp
  rw [hf]
  simp [Finset.card_powersetCard, nsmul_eq_mul]

/-- Lemma 4.2: exact polynomial for the actual restricted sumsets of H. -/
theorem sharedBlockPolynomial_formula (m u : ℕ) (hm : 2 ≤ m) :
    sharedBlockPolynomial m u = ∑ j ∈ range (u+1),
      (u.choose j : Polynomial ℤ) * ((1+X)^m-X-X^(m-1))^(u-j) * ambiguityPolynomial m j := by
  rw [sharedBlockPolynomial_by_ambiguous_set m u hm,
    sum_finsets_by_card u (fun j => (rowPolynomial m)^(u-j)*ambiguityPolynomial m j)]
  rw [rowPolynomial_eq m hm]
  apply Finset.sum_congr rfl
  intro j _
  ring

end SumsetRanges
