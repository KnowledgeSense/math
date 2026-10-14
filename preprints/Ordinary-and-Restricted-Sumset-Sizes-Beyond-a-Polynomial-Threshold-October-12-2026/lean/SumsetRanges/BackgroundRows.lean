import SumsetRanges.WeightedEnumeration

open Finset Polynomial
namespace SumsetRanges

abbrev UnambiguousRow (m : ℕ) :=
  {S : Finset (RowIndex m) // S≠rowAlpha m ∧ S≠rowBeta m}

noncomputable def validRowsEquiv {m u : ℕ} (J : Finset (Fin u)) :
    {R : Fin u → Finset (RowIndex m) // ValidRows J R} ≃
      ({i : Fin u // i ∉ J} → UnambiguousRow m) where
  toFun R i := ⟨R.val i.val, R.property.2 i.val i.property⟩
  invFun F := ⟨fun i => if hi : i ∈ J then ∅ else (F ⟨i,hi⟩).val, by
    constructor
    · intro i hi
      simp [hi]
    · intro i hi
      simp only [dite_eq_right hi]
      exact (F ⟨i,hi⟩).property⟩
  left_inv R := by
    apply Subtype.ext
    funext i
    by_cases hi : i∈J
    · simp [hi,R.property.1 i hi]
    · simp [hi]
  right_inv F := by
    funext i
    apply Subtype.ext
    simp [i.property]

noncomputable instance validRowsFintype (m u : ℕ) (J : Finset (Fin u)) :
    Fintype {R : Fin u → Finset (RowIndex m) // ValidRows J R} := by
  classical
  infer_instance

theorem background_weightPolynomial (m u : ℕ) (J : Finset (Fin u)) :
    weightPolynomial (fun R : {R : Fin u → Finset (RowIndex m) // ValidRows J R} =>
      ∑ i ∈ Finset.univ.filter (fun i => i ∉ J), (R.val i).card) =
      (rowPolynomial m)^(u-J.card) := by
  classical
  let w : ({i : Fin u // i ∉ J} → UnambiguousRow m) → ℕ :=
    fun F => ∑ i, (F i).val.card
  have hw : (fun R : {R : Fin u → Finset (RowIndex m) // ValidRows J R} =>
      ∑ i ∈ Finset.univ.filter (fun i => i ∉ J), (R.val i).card) = w ∘ validRowsEquiv J := by
    funext R
    exact Finset.sum_subtype _ (by simp) _
  rw [hw,weightPolynomial_equiv]
  unfold w
  rw [weightPolynomial_pi (fun (_ : {i : Fin u // i ∉ J}) (S : UnambiguousRow m) => S.val.card)]
  change (∏ _ : {i : Fin u // i ∉ J}, rowPolynomial m) = _
  simp only [Finset.prod_const, Finset.card_univ]
  congr 1
  rw [Fintype.card_subtype_compl]
  simp

end SumsetRanges
