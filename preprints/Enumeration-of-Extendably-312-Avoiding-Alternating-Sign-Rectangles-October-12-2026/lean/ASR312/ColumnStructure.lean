import ASR312.SquareBridge

namespace ASR312

 theorem firstColumn_nonnegative {r k : ℕ} (A : Rectangle r (k+1)) (h : IsASR A) (i : Fin r) :
    0 ≤ (A i 0).value := by
  have hh := firstColumn_not_minus A h i
  cases he : A i 0 <;> simp_all [Entry.value]

 theorem firstColumn_plus_unique {r k : ℕ} (A : Rectangle r (k+1)) (h : IsASR A)
    {i j : Fin r} (hi : A i 0 = .plus) (hj : A j 0 = .plus) : i = j := by
  classical
  by_contra hij
  have hh : (∑ t ∈ ({i,j} : Finset (Fin r)), (A t 0).value) ≤ ∑ t, (A t 0).value := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro t _ _
    exact firstColumn_nonnegative A h t
  have hc := (column_sum_bounds (col A 0) (h.2 0).1 (h.2 0).2).2
  rw [col_entrySum] at hc
  have hv : (∑ t ∈ ({i,j} : Finset (Fin r)), (A t 0).value) = 2 := by
    simp [hij,hi,hj,Entry.value]
  rw [hv] at hh
  omega

 theorem firstColumn_shape {r k : ℕ} (A : Rectangle r (k+1)) (h : IsASR A) :
    (∀ i, A i 0 = .zero) ∨ ∃ i, A i 0 = .plus ∧ ∀ j, j ≠ i → A j 0 = .zero := by
  classical
  by_cases hz : ∀ i, A i 0 = .zero
  · exact Or.inl hz
  · have hn : ∃ i, A i 0 ≠ .zero := by simpa using hz
    obtain ⟨i,hi⟩ := hn
    have hp : A i 0 = .plus := by
      have hm := firstColumn_not_minus A h i
      cases he : A i 0 <;> simp_all
    refine Or.inr ⟨i,hp,?_⟩
    intro j hji
    have hm := firstColumn_not_minus A h j
    have hn : A j 0 ≠ .plus := fun hj => hji (firstColumn_plus_unique A h hj hp)
    cases he : A j 0 <;> simp_all

end ASR312
