import ASR312.GappedCompletion

namespace ASR312

theorem gappedCompletion_asm {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m)
    (ha : IsASR A) (hn : nonemptyRows A = r) : IsASM (gappedCompletion A hc s hs) := by
  have hrows (i : Fin (r+n)) : Alternates (row (gappedCompletion A hc s hs) i) ∧
      StartsPositive (row (gappedCompletion A hc s hs) i) ∧ EndsPositive (row (gappedCompletion A hc s hs) i) := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Alternates,StartsPositive,EndsPositive,gappedCompletion_row_top] using ha.1 i
    · simp [Alternates,StartsPositive,EndsPositive,gappedCompletion_row_bottom]
  have hcols (j : Fin (r+n)) : Alternates (col (gappedCompletion A hc s hs) j) ∧
      StartsPositive (col (gappedCompletion A hc s hs) j) := by
    classical
    by_cases hj : j.val < r+m
    · by_cases hz : (⟨j.val,hj⟩ : Fin (r+m)) ∈ zeroSumColumns A
      · simp only [Alternates,StartsPositive,gappedCompletion_col_small A hc s hs j hj,hz,ite_true]
        refine ⟨column_append_plus_chain _ (ha.2 _).1 (ha.2 _).2 ((mem_zeroSumColumns A _).mp hz),?_⟩
        have hstart := (ha.2 ⟨j.val,hj⟩).2
        cases hl : nonzeroEntries (col A ⟨j.val,hj⟩) with
        | nil => simp
        | cons x l => simpa only [StartsPositive,hl,List.cons_append,List.head?_cons] using hstart
      · simpa only [Alternates,StartsPositive,gappedCompletion_col_small A hc s hs j hj,hz,ite_false,List.append_nil]
          using ha.2 ⟨j.val,hj⟩
    · simp [Alternates,StartsPositive,gappedCompletion_col_large A hc s hs j (by omega)]
  apply square_rowcomplete_asm _ ⟨hrows,hcols⟩
  apply (nonemptyRows_eq_rows_iff _).mpr
  intro i
  apply (exists_nonzero_iff _).mp
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [show nonzeroEntries (List.ofFn (gappedCompletion A hc s hs (i.castAdd n))) =
        nonzeroEntries (row A i) from gappedCompletion_row_top A hc s hs i]
    exact (exists_nonzero_iff _).mpr ((nonemptyRows_eq_rows_iff A).mp hn i)
  · have hh := gappedCompletion_row_bottom A hc s hs i
    change nonzeroEntries (row (gappedCompletion A hc s hs) (i.natAdd r)) ≠ []
    rw [hh]
    simp

theorem gappedCompletion_avoids {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m)
    (he : ExtendablyAvoids312 A) : Avoids312 (gappedCompletion A hc s hs) := by
  rintro ⟨i₁,i₂,i₃,j₁,j₂,j₃,h12,h23,hj12,hj23,h13,h21,h32⟩
  have top (i j : Fin (r+n)) (hi : i.val < r) (hp : gappedCompletion A hc s hs i j = .plus) :
      ∃ hj : j.val < r+m, A ⟨i.val,hi⟩ ⟨j.val,hj⟩ = .plus := by
    have hei : i = (⟨i.val,hi⟩ : Fin r).castAdd n := Fin.ext rfl
    have hh := (congrArg (fun q => gappedCompletion A hc s hs q j) hei).symm.trans hp
    simp only [gappedCompletion,Fin.append_left] at hh
    by_cases hj : j.val < r+m
    · exact ⟨hj,by simpa only [hj,dite_true] using hh⟩
    · simp only [hj,dite_false] at hh
      cases hh
  have bottom (i j : Fin (r+n)) (hi : r ≤ i.val) (hp : gappedCompletion A hc s hs i j = .plus) :
      j = gappedColumn A hc s hs ⟨i.val-r,by omega⟩ := by
    have hei : i = (⟨i.val-r,by omega⟩ : Fin n).natAdd r := Fin.ext (by simp; omega)
    rw [hei] at hp
    simp only [gappedCompletion,Fin.append_right] at hp
    simpa using hp
  by_cases h3 : i₃.val < r
  · have h2 : i₂.val < r := by change i₂.val < i₃.val at h23; omega
    have h1 : i₁.val < r := by change i₁.val < i₂.val at h12; omega
    obtain ⟨hj3,hA13⟩ := top i₁ j₃ h1 h13
    obtain ⟨hj1,hA21⟩ := top i₂ j₁ h2 h21
    obtain ⟨hj2,hA32⟩ := top i₃ j₂ h3 h32
    exact extendable_implies_avoids he ⟨⟨i₁.val,h1⟩,⟨i₂.val,h2⟩,⟨i₃.val,h3⟩,
      ⟨j₁.val,hj1⟩,⟨j₂.val,hj2⟩,⟨j₃.val,hj3⟩,h12,h23,hj12,hj23,hA13,hA21,hA32⟩
  · have h3' : r ≤ i₃.val := by omega
    have he3 := bottom i₃ j₂ h3' h32
    by_cases h2 : i₂.val < r
    · have h1 : i₁.val < r := by change i₁.val < i₂.val at h12; omega
      obtain ⟨hj3,hA13⟩ := top i₁ j₃ h1 h13
      obtain ⟨hj1,hA21⟩ := top i₂ j₁ h2 h21
      have hj2 : j₂.val < r+m := by change j₂.val < j₃.val at hj23; omega
      have hmem := (gappedColumn_small_range_iff A hc s hs ⟨j₂.val,hj2⟩).mp
        ⟨⟨i₃.val-r,by omega⟩,congrArg Fin.val he3.symm⟩
      exact extendable_no_cross_zero_column A he ⟨i₁.val,h1⟩ ⟨i₂.val,h2⟩
        ⟨j₁.val,hj1⟩ ⟨j₂.val,hj2⟩ ⟨j₃.val,hj3⟩ h12 hj12 hj23 hA13 hA21
        ((mem_zeroSumColumns A _).mp hmem)
    · have h2' : r ≤ i₂.val := by omega
      have he2 := bottom i₂ j₁ h2' h21
      by_cases hj2 : j₂.val < r+m
      · have hj1 : j₁.val < r+m := by change j₁.val < j₂.val at hj12; omega
        have hm2 := (gappedColumn_lt_iff A hc s hs ⟨i₂.val-r,by omega⟩).mp (by rw [← he2]; exact hj1)
        have hm3 := (gappedColumn_lt_iff A hc s hs ⟨i₃.val-r,by omega⟩).mp (by rw [← he3]; exact hj2)
        have hh := gappedColumn_small_anti A hc s hs ⟨i₂.val-r,by omega⟩ ⟨i₃.val-r,by omega⟩
          (by change i₂.val-r < i₃.val-r; change i₂.val < i₃.val at h23; omega) hm2 hm3
        rw [← he2,← he3] at hh
        exact (not_lt_of_ge hh.le) hj12
      · have h1' : r ≤ i₁.val := by
          by_contra hn
          obtain ⟨hj3,_⟩ := top i₁ j₃ (by omega) h13
          change j₂.val < j₃.val at hj23
          omega
        have he1 := bottom i₁ j₃ h1' h13
        have hj3 : ¬j₃.val < r+m := by change j₂.val < j₃.val at hj23; omega
        have hm1 : (⟨i₁.val-r,by omega⟩ : Fin n) ∉ s := by
          rw [← gappedColumn_lt_iff A hc s hs,← he1]; exact hj3
        have hm3 : (⟨i₃.val-r,by omega⟩ : Fin n) ∉ s := by
          rw [← gappedColumn_lt_iff A hc s hs,← he3]; exact hj2
        have hh := gappedColumn_large_mono A hc s hs ⟨i₁.val-r,by omega⟩ ⟨i₃.val-r,by omega⟩
          (by change i₁.val-r < i₃.val-r; have hx := lt_trans h12 h23; change i₁.val < i₃.val at hx; omega) hm1 hm3
        rw [← he1,← he3] at hh
        exact (not_lt_of_ge hh.le) hj23

end ASR312
