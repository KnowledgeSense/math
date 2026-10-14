import ASR312.PivotInsert

namespace ASR312

 theorem nonzeroEntries_of_no_minus_sum_one {n : ℕ} (f : Fin n → Entry)
    (hm : ∀ j, f j ≠ .minus) (hs : ∑ j, (f j).value = 1) :
    nonzeroEntries (List.ofFn f) = [.plus] := by
  classical
  have he : minusPositions f = ∅ := by simp [minusPositions,hm]
  have hc := entry_sum_counts f
  rw [he,Finset.card_empty,hs] at hc
  have hp : (plusPositions f).card = 1 := by omega
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp hp
  have hzp : f z = .plus := by
    have hmem : z ∈ plusPositions f := by rw [hz]; simp
    exact (Finset.mem_filter.mp hmem).2
  have hf : f = (fun j => if j = z then Entry.plus else .zero) := by
    funext j
    by_cases hj : j = z
    · subst j; simp [hzp]
    · have hnot : f j ≠ .plus := by
        intro h
        have hmem : j ∈ plusPositions f := by simp [plusPositions,h]
        rw [hz] at hmem
        exact hj (Finset.mem_singleton.mp hmem)
      have hn := hm j
      rw [ite_eq_right hj]
      cases he : f j with
      | minus => exact False.elim (hn he)
      | zero => rfl
      | plus => exact False.elim (hnot he)
  rw [hf]
  exact nonzero_ofFn_single z

 theorem asm_first_row_entries {n : ℕ} (A : Rectangle (n+1) (n+1)) (ha : IsASM A) :
    nonzeroEntries (row A 0) = [.plus] := by
  apply nonzeroEntries_of_no_minus_sum_one
  · intro j
    have hs := (ha.1.2 j).2
    rw [col,List.ofFn_succ] at hs
    exact startsPositive_cons_not_minus hs
  · obtain ⟨j,hj⟩ := asm_row_exists_plus A ha 0
    exact row_sum_of_plus A ha.1 0 hj

 theorem asm_first_col_entries {n : ℕ} (A : Rectangle (n+1) (n+1)) (ha : IsASM A) :
    nonzeroEntries (col A 0) = [.plus] :=
  nonzeroEntries_of_no_minus_sum_one (fun j => A j 0)
    (firstColumn_not_minus A ha.1) (asm_column_sum A ha 0)

 theorem asm_first_row_tail_entries {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hz : A 0 0 = .zero) :
    nonzeroEntries (List.ofFn (fun j : Fin n => A 0 j.succ)) = [.plus] := by
  have hh := asm_first_row_entries A ha
  simpa [row,List.ofFn_succ,nonzeroEntries,hz] using hh

 theorem asm_first_col_tail_entries {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hz : A 0 0 = .zero) :
    nonzeroEntries (List.ofFn (fun i : Fin n => A i.succ 0)) = [.plus] := by
  have hh := asm_first_col_entries A ha
  simpa [col,List.ofFn_succ,nonzeroEntries,hz] using hh

end ASR312
