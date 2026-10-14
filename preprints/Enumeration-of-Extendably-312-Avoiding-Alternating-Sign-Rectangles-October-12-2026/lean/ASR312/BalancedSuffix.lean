import ASR312.RowSlices

namespace ASR312

theorem balancedSuffix_no_minus {p n k : ℕ} (A : Rectangle (p+(n+1)) k)
    (he : ExtendablyAvoids312 A) (hz : ∀ j, A ((0 : Fin (n+1)).natAdd p) j = .zero)
    (i : Fin (n+1)) (j : Fin k) : rowSuffix A i j ≠ .minus := by
  refine Fin.cases ?_ (fun i => ?_) i
  · change A ((0 : Fin (n+1)).natAdd p) j ≠ .minus
    rw [hz]
    decide
  · exact afterEmptyRow_no_minus A he _ hz _ j (by change p < p+(i.val+1); omega)

theorem balancedSuffix_sparse {p n k : ℕ} (A : Rectangle (p+(n+1)) k)
    (ha : IsASR A) (he : ExtendablyAvoids312 A) (hn : nonemptyRows A = k)
    (hz : ∀ j, A ((0 : Fin (n+1)).natAdd p) j = .zero) : SparseDescending (rowSuffix A) := by
  have hm := balancedSuffix_no_minus A he hz
  have hcol (i t : Fin (n+1)) (j : Fin k) (hi : rowSuffix A i j = .plus)
      (ht : rowSuffix A t j = .plus) : i = t := by
    apply noMinus_sum_le_one_unique (fun i => rowSuffix A i j) (fun i => hm i j) _ hi ht
    have hs := rowSlices_col_sum A j
    rw [balanced_column_sums A ha hn j] at hs
    have hpre := (column_sum_bounds _ ((rowPrefix_asr A ha).2 j).1 ((rowPrefix_asr A ha).2 j).2).1
    rw [← col_entrySum]
    omega
  refine ⟨hm,?_,hcol,?_⟩
  · intro i j u hij hiu
    apply noMinus_sum_le_one_unique ((rowSuffix A) i) (hm i) _ hij hiu
    have hs := row_sum_of_plus A ha (i.natAdd p) hij
    exact hs.le
  · intro i t j u hit hij htu
    have hi0 : i ≠ 0 := by
      intro h
      subst i
      change A ((0 : Fin (n+1)).natAdd p) j = .plus at hij
      rw [hz] at hij
      cases hij
    rcases lt_trichotomy j u with h | h | h
    · exact False.elim (afterEmptyRow_descending A he _ hz (i.natAdd p) (t.natAdd p) j u
        (by change p < p+i.val; have hh := Fin.pos_iff_ne_zero.mpr hi0; omega) (by simpa using hit) h hij htu)
    · subst u
      exact False.elim ((ne_of_lt hit) (hcol i t j hij htu))
    · exact h

theorem balancedSuffix_columnSupport {p n k : ℕ} (A : Rectangle (p+(n+1)) k)
    (ha : IsASR A) (he : ExtendablyAvoids312 A) (hn : nonemptyRows A = k)
    (hz : ∀ j, A ((0 : Fin (n+1)).natAdd p) j = .zero) :
    columnSupport (rowSuffix A) = zeroSumColumns (rowPrefix A) := by
  classical
  ext j
  rw [mem_columnSupport,mem_zeroSumColumns]
  have hm := balancedSuffix_no_minus A he hz
  have hs := rowSlices_col_sum A j
  rw [balanced_column_sums A ha hn j] at hs
  have hb := column_sum_bounds _ ((rowPrefix_asr A ha).2 j).1 ((rowPrefix_asr A ha).2 j).2
  have hminus : minusPositions (fun i => rowSuffix A i j) = ∅ := by
    ext i
    simp [minusPositions,hm i j]
  have hc := entry_sum_counts (fun i => rowSuffix A i j)
  rw [hminus,Finset.card_empty,← col_entrySum] at hc
  have hex : (∃ i, rowSuffix A i j = .plus) ↔ 0 < (plusPositions (fun i => rowSuffix A i j)).card := by
    rw [Finset.card_pos]
    simp [Finset.Nonempty,plusPositions]
  rw [hex]
  omega

theorem balanced_eq_of_prefix_suffixSupport {p n k : ℕ} (A B : Rectangle (p+(n+1)) k)
    (ha : IsASR A) (he : ExtendablyAvoids312 A) (hn : nonemptyRows A = k)
    (hz : ∀ j, A ((0 : Fin (n+1)).natAdd p) j = .zero)
    (hb : IsASR B) (hbe : ExtendablyAvoids312 B) (hbn : nonemptyRows B = k)
    (hbz : ∀ j, B ((0 : Fin (n+1)).natAdd p) j = .zero)
    (hp : rowPrefix A = rowPrefix B) (hr : rowSupport (rowSuffix A) = rowSupport (rowSuffix B)) : A = B := by
  have hc : columnSupport (rowSuffix A) = columnSupport (rowSuffix B) := by
    rw [balancedSuffix_columnSupport A ha he hn hz,balancedSuffix_columnSupport B hb hbe hbn hbz,hp]
  have hs := sparseDescending_eq_of_supports (rowSuffix A) (rowSuffix B)
    (balancedSuffix_sparse A ha he hn hz) (balancedSuffix_sparse B hb hbe hbn hbz) hr hc
  rw [← rowSlices_reconstruction A,← rowSlices_reconstruction B,hp,hs]

end ASR312
