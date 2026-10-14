import ASR312.RectanglePureEquivalence

namespace ASR312

theorem extendable_asr_of_ends {r k : ℕ} (A : Rectangle r k)
    (he : ExtendablyAvoids312 A) (hend : ∀ i, EndsPositive (row A i)) : IsASR A := by
  obtain ⟨n,hr,hk,B,hB,_,hmatch⟩ := he
  have hrow (i : Fin r) : row A i <+: row B (Fin.castLE hr i) := by
    have hh : row A i = (row B (Fin.castLE hr i)).take k := by
      simp only [row]
      rw [take_ofFn hk]
      congr 1
      funext j
      exact (hmatch i j).symm
    rw [hh]
    exact List.take_prefix _ _
  have hcol (j : Fin k) : col A j <+: col B (Fin.castLE hk j) := by
    have hh : col A j = (col B (Fin.castLE hk j)).take r := by
      simp only [col]
      rw [take_ofFn hr]
      congr 1
      funext i
      exact (hmatch i j).symm
    rw [hh]
    exact List.take_prefix _ _
  exact ⟨fun i => ⟨alternates_prefix (hrow i) (hB.1.1 _).1,
      startsPositive_prefix (hrow i) (hB.1.1 _).2.1,hend i⟩,
    fun j => ⟨alternates_prefix (hcol j) (hB.1.2 _).1,
      startsPositive_prefix (hcol j) (hB.1.2 _).2⟩⟩

theorem asr_firstRow_no_minus {r k : ℕ} (A : Rectangle (r+1) k)
    (ha : IsASR A) (j : Fin k) : A 0 j ≠ .minus := by
  have hh := (ha.2 j).2
  rw [col,List.ofFn_succ] at hh
  exact startsPositive_cons_not_minus hh

theorem asr_firstRow_entries {r k : ℕ} (A : Rectangle (r+1) k)
    (ha : IsASR A) (hn : ∃ j, A 0 j ≠ .zero) :
    nonzeroEntries (row A 0) = [.plus] := by
  obtain ⟨j,hj⟩ := hn
  have hp : A 0 j = .plus := by
    have hm := asr_firstRow_no_minus A ha j
    cases hx : A 0 j <;> simp_all
  exact nonzeroEntries_of_no_minus_sum_one _ (asr_firstRow_no_minus A ha)
    (row_sum_of_plus A ha 0 hp)

theorem asr_firstRow_tail_entries {r k : ℕ} (A : Rectangle (r+1) (k+1))
    (ha : IsASR A) (hn : ∃ j, A 0 j ≠ .zero) (hz : A 0 0 = .zero) :
    nonzeroEntries (List.ofFn (fun j : Fin k => A 0 j.succ)) = [.plus] := by
  have hh := asr_firstRow_entries A ha hn
  simpa [row,List.ofFn_succ,nonzeroEntries,hz] using hh

theorem extendable_firstRow_entries {r k : ℕ} (A : Rectangle (r+1) k)
    (he : ExtendablyAvoids312 A) (hn : ∃ j, A 0 j ≠ .zero) :
    nonzeroEntries (row A 0) = [.plus] := by
  obtain ⟨n,hr,hk,B,hB,_,hmatch⟩ := he
  cases n with
  | zero => omega
  | succ n =>
    have hi : Fin.castLE hr 0 = (0 : Fin (n+1)) := Fin.ext rfl
    obtain ⟨j,hj⟩ := hn
    have hp : B 0 (Fin.castLE hk j) = .plus := by
      have hh := hmatch 0 j
      rw [hi] at hh
      have hm := asm_first_row_no_minus B hB (Fin.castLE hk j)
      cases hx : B 0 (Fin.castLE hk j) with
      | minus => exact False.elim (hm hx)
      | zero => exact False.elim (hj (hh.symm.trans hx))
      | plus => rfl
    have hf : A 0 = fun u => if u = j then Entry.plus else .zero := by
      funext u
      have hh := hmatch 0 u
      rw [hi] at hh
      by_cases hu : u = j
      · subst u; simpa [hp] using hh.symm
      · have hne : Fin.castLE hk u ≠ Fin.castLE hk j := by
          intro h
          exact hu (Fin.ext (congrArg (fun q : Fin (n+1) => q.val) h))
        rw [asm_first_row_unique_plus B hB _ _ hp hne] at hh
        simpa [hu] using hh.symm
    rw [row,hf]
    exact nonzero_ofFn_single j

end ASR312
