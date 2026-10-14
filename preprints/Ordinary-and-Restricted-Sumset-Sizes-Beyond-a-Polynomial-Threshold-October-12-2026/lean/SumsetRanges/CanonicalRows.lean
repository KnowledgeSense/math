import SumsetRanges.RowAssembly

open Finset
namespace SumsetRanges

noncomputable def chosenRows {u : ℕ} (J : Finset (Fin u)) (p : ℕ) : Finset (Fin u) :=
  Classical.choose (Finset.exists_subset_card_eq (s := J) (Nat.min_le_right p J.card))

theorem chosenRows_subset {u : ℕ} (J : Finset (Fin u)) (p : ℕ) : chosenRows J p ⊆ J :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (s := J) (Nat.min_le_right p J.card))).1

theorem card_chosenRows {u : ℕ} (J : Finset (Fin u)) (p : ℕ) (hp : p ≤ J.card) :
    (chosenRows J p).card = p := by
  have h := (Classical.choose_spec (Finset.exists_subset_card_eq (s := J)
    (Nat.min_le_right p J.card))).2
  simpa [chosenRows, Nat.min_eq_left hp] using h

noncomputable def canonicalRows {m u : ℕ} (J : Finset (Fin u))
    (R : Fin u → Finset (RowIndex m)) (p : ℕ) (i : Fin u) : Finset (RowIndex m) :=
  if i ∈ J then if i ∈ chosenRows J p then rowAlpha m else rowBeta m else R i

theorem rowValue_canonicalRows {m u : ℕ} (J : Finset (Fin u))
    (R : Fin u → Finset (RowIndex m)) (p : ℕ) (i : Fin u) :
    rowValue (canonicalRows J R p i) = if i ∈ J then (fun _ => 1) else rowValue (R i) := by
  unfold canonicalRows
  by_cases hi : i ∈ J
  · rw [ite_eq_left hi, ite_eq_left hi]
    split <;> simp
  · rw [ite_eq_right hi, ite_eq_right hi]

theorem alphaRows_canonicalRows {m u : ℕ} (J : Finset (Fin u))
    (R : Fin u → Finset (RowIndex m)) (p : ℕ) :
    Finset.univ.filter (fun i => none ∈ canonicalRows J R p i) =
      chosenRows J p ∪ (Finset.univ.filter (fun i => i ∉ J ∧ none ∈ R i)) := by
  ext i
  have hc := chosenRows_subset J p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  by_cases hi : i ∈ J
  · by_cases hp : i ∈ chosenRows J p <;> simp [canonicalRows, hi, hp]
  · have hp : i ∉ chosenRows J p := fun h => hi (hc h)
    simp [canonicalRows, hi, hp]

theorem alphaCount_canonicalRows {m u : ℕ} (J : Finset (Fin u))
    (R : Fin u → Finset (RowIndex m)) (p : ℕ) (hp : p ≤ J.card) :
    (Finset.univ.filter (fun i => none ∈ canonicalRows J R p i)).card =
      p + (Finset.univ.filter (fun i => i ∉ J ∧ none ∈ R i)).card := by
  rw [alphaRows_canonicalRows, Finset.card_union_of_disjoint, card_chosenRows J p hp]
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact (Finset.mem_filter.mp hj).2.1 (chosenRows_subset J p hi)

def ambiguousRows {m u : ℕ} (R : Fin u → Finset (RowIndex m)) : Finset (Fin u) :=
  Finset.univ.filter (fun i => R i=rowAlpha m ∨ R i=rowBeta m)

def ambiguousAlphaRows {m u : ℕ} (R : Fin u → Finset (RowIndex m)) : Finset (Fin u) :=
  Finset.univ.filter (fun i => R i=rowAlpha m)

theorem ambiguousAlphaRows_subset {m u : ℕ} (R : Fin u → Finset (RowIndex m)) :
    ambiguousAlphaRows R ⊆ ambiguousRows R := by
  intro i hi
  simp only [ambiguousAlphaRows, ambiguousRows, Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact Or.inl hi

theorem alphaRows_partition {m u : ℕ} (R : Fin u → Finset (RowIndex m)) :
    Finset.univ.filter (fun i => none ∈ R i) = ambiguousAlphaRows R ∪
      Finset.univ.filter (fun i => i ∉ ambiguousRows R ∧ none ∈ R i) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    ambiguousAlphaRows, ambiguousRows]
  constructor
  · intro hi
    by_cases he : R i = rowAlpha m
    · exact Or.inl he
    · right
      refine ⟨?_,hi⟩
      rintro (h | h)
      · exact he h
      · rw [h] at hi
        simp at hi
  · rintro (h | ⟨_,h⟩)
    · rw [h]; simp
    · exact h

/-- Every actual shared-block subset sum has a canonical representative obtained
 by retaining each unambiguous row and recording only the number of alpha rows
 among the ambiguous rows. -/
theorem canonicalRows_same_sum {m u : ℕ} (R : Fin u → Finset (RowIndex m)) :
    ∑ a ∈ assembleRows (canonicalRows (ambiguousRows R) R (ambiguousAlphaRows R).card), sharedPoint a =
      ∑ a ∈ assembleRows R, sharedPoint a := by
  rw [assembled_rows_collision]
  constructor
  · rw [alphaCount_canonicalRows _ _ _ (Finset.card_le_card (ambiguousAlphaRows_subset R))]
    rw [alphaRows_partition R, Finset.card_union_of_disjoint]
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_filter.mp hj).2.1 (ambiguousAlphaRows_subset R hi)
  · intro i
    rw [rowValue_canonicalRows]
    by_cases hi : i ∈ ambiguousRows R
    · rw [ite_eq_left hi]
      have hh := (Finset.mem_filter.mp hi).2
      rcases hh with hh | hh <;> rw [hh] <;> simp
    · rw [ite_eq_right hi]

theorem canonicalRows_sum_injective_parameter {m u : ℕ} (J : Finset (Fin u))
    (R : Fin u → Finset (RowIndex m)) (p q : ℕ) (hp : p ≤ J.card) (hq : q ≤ J.card) :
    (∑ a ∈ assembleRows (canonicalRows J R p), sharedPoint a =
      ∑ a ∈ assembleRows (canonicalRows J R q), sharedPoint a) ↔ p=q := by
  rw [assembled_rows_collision]
  rw [alphaCount_canonicalRows J R p hp, alphaCount_canonicalRows J R q hq]
  constructor
  · rintro ⟨h,_⟩
    omega
  · intro h
    subst q
    exact ⟨rfl, fun _ => rfl⟩

theorem card_canonicalRows {m u : ℕ} (J : Finset (Fin u))
    (R : Fin u → Finset (RowIndex m)) (p : ℕ) (hp : p ≤ J.card) :
    (assembleRows (canonicalRows J R p)).card =
      p+(J.card-p)*(m-1) + ∑ i ∈ Finset.univ.filter (fun i => i ∉ J), (R i).card := by
  rw [card_assembleRows]
  have he (i : Fin u) : (canonicalRows J R p i).card =
      if i ∈ J then if i ∈ chosenRows J p then 1 else m-1 else (R i).card := by
    unfold canonicalRows
    split_ifs <;> simp
  simp only [he]
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  congr 1
  rw [Finset.sum_ite]
  have hf : J.filter (fun i => i ∈ chosenRows J p) = chosenRows J p := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨chosenRows_subset J p h,h⟩⟩
  have hn : J.filter (fun i => i ∉ chosenRows J p) = J \ chosenRows J p := by
    ext i
    simp
  rw [hf, hn]
  simp only [Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_sdiff_of_subset (chosenRows_subset J p), card_chosenRows J p hp]

def ValidRows {m u : ℕ} (J : Finset (Fin u)) (R : Fin u → Finset (RowIndex m)) : Prop :=
  (∀ i ∈ J, R i=∅) ∧ (∀ i ∉ J, R i≠rowAlpha m ∧ R i≠rowBeta m)

theorem ambiguous_canonicalRows {m u : ℕ} (J : Finset (Fin u))
    (R : Fin u → Finset (RowIndex m)) (p : ℕ) (hR : ValidRows J R) :
    ambiguousRows (canonicalRows J R p) = J := by
  ext i
  simp only [ambiguousRows, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i∈J
  · simp only [canonicalRows, ite_eq_left hi]
    split <;> simp [hi]
  · simp only [canonicalRows, ite_eq_right hi]
    exact ⟨fun h => h.elim (fun h => False.elim ((hR.2 i hi).1 h))
      (fun h => False.elim ((hR.2 i hi).2 h)), False.elim ∘ hi⟩

theorem canonicalRows_data_injective {m u : ℕ} (J K : Finset (Fin u))
    (R T : Fin u → Finset (RowIndex m)) (p q : ℕ)
    (hR : ValidRows J R) (hT : ValidRows K T) (hp : p≤J.card) (hq : q≤K.card)
    (he : ∑ a ∈ assembleRows (canonicalRows J R p), sharedPoint a =
      ∑ a ∈ assembleRows (canonicalRows K T q), sharedPoint a) :
    J=K ∧ R=T ∧ p=q := by
  have hrows := (assembled_rows_collision _ _).mp he
  have hJK : J=K := by
    rw [← ambiguous_canonicalRows J R p hR, ← ambiguous_canonicalRows K T q hT]
    ext i
    simp only [ambiguousRows, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← rowValue_eq_one_iff, ← rowValue_eq_one_iff, hrows.2 i]
  subst K
  have hRT : R=T := by
    funext i
    by_cases hi : i∈J
    · rw [hR.1 i hi,hT.1 i hi]
    · have hr := hrows.2 i
      rw [rowValue_canonicalRows, rowValue_canonicalRows, ite_eq_right hi, ite_eq_right hi] at hr
      rcases rowValue_collision (R i) (T i) hr with h | ⟨h,_⟩ | ⟨h,_⟩
      · exact h
      · exact False.elim ((hR.2 i hi).1 h)
      · exact False.elim ((hR.2 i hi).2 h)
  subst T
  refine ⟨rfl,rfl,?_⟩
  exact (canonicalRows_sum_injective_parameter J R p q hp hq).mp he

end SumsetRanges
