import ASR312.RectangleRecurrence

namespace ASR312

theorem column_sum_zero_last (l : List Entry) (ha : Alternates l)
    (hs : StartsPositive l) (hv : entrySum l = 0) :
    (nonzeroEntries l).getLast? = none ∨ (nonzeroEntries l).getLast? = some .minus := by
  have hh := alternating_sum_endpoints (nonzeroEntries l) ha (nonzeroEntries_ne_zero l)
  rw [nonzeroEntries_sum,hv] at hh
  rcases hs with hs | hs
  · have he : nonzeroEntries l = [] := List.head?_eq_none_iff.mp hs
    simp [he]
  · rw [hs] at hh
    cases he : (nonzeroEntries l).getLast? with
    | none => exact Or.inl rfl
    | some e =>
      right
      rw [he] at hh
      cases e <;> simp_all [endValue,Entry.value]

theorem column_append_plus_chain (l : List Entry) (ha : Alternates l)
    (hs : StartsPositive l) (hv : entrySum l = 0) :
    (nonzeroEntries l ++ [Entry.plus]).IsChain (· ≠ ·) := by
  apply ha.append (by simp)
  intro x hx y hy
  simp only [List.head?_cons,Option.mem_def,Option.some.injEq] at hy
  subst y
  rcases column_sum_zero_last l ha hs hv with he | he
  · simp [he] at hx
  · have hx : Entry.minus = x := by simpa [he] using hx
    subst x
    decide

noncomputable def zeroSumColumns {r k : ℕ} (A : Rectangle r k) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (fun j => entrySum (col A j) = 0)

theorem mem_zeroSumColumns {r k : ℕ} (A : Rectangle r k) (j : Fin k) :
    j ∈ zeroSumColumns A ↔ entrySum (col A j) = 0 := by
  classical
  simp [zeroSumColumns]

theorem zeroSumColumns_card {r k : ℕ} (A : Rectangle r k) (ha : IsASR A) :
    (zeroSumColumns A).card + nonemptyRows A = k := by
  classical
  have hv (j : Fin k) : entrySum (col A j) =
      if j ∈ zeroSumColumns A then (0 : ℤ) else 1 := by
    have hb := column_sum_bounds _ (ha.2 j).1 (ha.2 j).2
    by_cases h : j ∈ zeroSumColumns A
    · simp only [h,ite_true]
      exact (mem_zeroSumColumns A j).mp h
    · simp only [h,ite_false]
      have hn : entrySum (col A j) ≠ 0 := by simpa only [mem_zeroSumColumns] using h
      omega
  have hs : (∑ j, entrySum (col A j)) = (nonemptyRows A : ℤ) := by
    simp_rw [col_entrySum]
    rw [Finset.sum_comm,total_sum_nonemptyRows A ha]
  simp_rw [hv] at hs
  have hc : (∑ j : Fin k, if j ∈ zeroSumColumns A then (0 : ℤ) else 1) =
      ((zeroSumColumns A)ᶜ.card : ℤ) := by
    simp [Finset.sum_ite,Finset.filter_not,Finset.compl_eq_univ_sdiff]
  rw [hc,Finset.card_compl] at hs
  simp only [Fintype.card_fin] at hs
  have hb := Finset.card_le_univ (zeroSumColumns A)
  simp only [Fintype.card_fin] at hb
  omega

theorem zeroSumColumns_rowcomplete_card {r m : ℕ} (A : Rectangle r (r+m))
    (ha : IsASR A) (hn : nonemptyRows A = r) : (zeroSumColumns A).card = m := by
  have hh := zeroSumColumns_card A ha
  rw [hn] at hh
  omega

end ASR312
