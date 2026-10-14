import ASR312.RepairedBlock

namespace ASR312

 theorem exists_nonzero_iff {n : ℕ} (f : Fin n → Entry) :
    nonzeroEntries (List.ofFn f) ≠ [] ↔ ∃ j, f j ≠ .zero := by
  have he : nonzeroEntries (List.ofFn f) = [] ↔ ∀ j, f j = .zero := by
    simp [nonzeroEntries,List.filter_eq_nil_iff]
  simpa only [not_forall] using not_congr he

 theorem repairedLowerBlock_row_entries {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin (n+1)) (hp : A p 0 = .plus)
    (i : Fin (n+1-p.val)) (hi : i.val ≠ 0) :
    nonzeroEntries (row (repairedLowerBlock A p) i) =
      nonzeroEntries (row A ⟨p.val+i.val,by omega⟩) := by
  have he : row (repairedLowerBlock A p) i = row (lowerBlock A p.val) i := by
    unfold row
    congr 1
    funext j
    simp [repairedLowerBlock,hi]
  rw [he,lowerBlock_row]
  apply nonzeroEntries_drop_ofFn
  intro j hj
  exact asm_below_left_zero A ha hav p hp _ j (by change p.val < p.val+i.val; omega) hj

 theorem repairedLowerBlock_col_entries {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin (n+1)) (hp : A p 0 = .plus)
    (j : Fin (n+1-p.val)) (hj : j.val ≠ 0) :
    nonzeroEntries (col (repairedLowerBlock A p) j) =
      nonzeroEntries (col A ⟨p.val+j.val,by omega⟩) := by
  have he : col (repairedLowerBlock A p) j = col (lowerBlock A p.val) j := by
    unfold col
    congr 1
    funext i
    simp [repairedLowerBlock,hj]
  rw [he,lowerBlock_col]
  apply nonzeroEntries_drop_ofFn
  intro i hi
  exact (asm_pivot_top_facts A ha hav p hp).1 i _ hi (by change p.val < p.val+j.val; omega)

 theorem repairedLowerBlock_asm {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin (n+1))
    (hp : A p 0 = .plus) (hz : A p p = .minus) : IsASM (repairedLowerBlock A p) := by
  have hr (i : Fin (n+1-p.val)) : Alternates (row (repairedLowerBlock A p) i) ∧
      StartsPositive (row (repairedLowerBlock A p) i) ∧ EndsPositive (row (repairedLowerBlock A p) i) ∧
      nonzeroEntries (row (repairedLowerBlock A p) i) ≠ [] := by
    by_cases hi : i.val = 0
    · have he : i = blockZero p := Fin.ext hi
      subst i
      simp [Alternates,StartsPositive,EndsPositive,repairedLowerBlock_first_row A ha hav p hp hz]
    · have he := repairedLowerBlock_row_entries A ha hav p hp i hi
      have hn : nonzeroEntries (row A ⟨p.val+i.val,by omega⟩) ≠ [] :=
        (exists_nonzero_iff _).mpr (ha.2.1 _)
      simpa only [Alternates,StartsPositive,EndsPositive,he] using
        ⟨(ha.1.1 ⟨p.val+i.val,by omega⟩).1,(ha.1.1 ⟨p.val+i.val,by omega⟩).2.1,
          (ha.1.1 ⟨p.val+i.val,by omega⟩).2.2,hn⟩
  have hc (j : Fin (n+1-p.val)) : Alternates (col (repairedLowerBlock A p) j) ∧
      StartsPositive (col (repairedLowerBlock A p) j) ∧ EndsPositive (col (repairedLowerBlock A p) j) ∧
      nonzeroEntries (col (repairedLowerBlock A p) j) ≠ [] := by
    by_cases hj : j.val = 0
    · have he : j = blockZero p := Fin.ext hj
      subst j
      simp [Alternates,StartsPositive,EndsPositive,repairedLowerBlock_first_col A ha hav p hz]
    · have he := repairedLowerBlock_col_entries A ha hav p hp j hj
      have hn : nonzeroEntries (col A ⟨p.val+j.val,by omega⟩) ≠ [] :=
        (exists_nonzero_iff _).mpr (ha.2.2 _).1
      simpa only [Alternates,StartsPositive,EndsPositive,he] using
        ⟨(ha.1.2 ⟨p.val+j.val,by omega⟩).1,(ha.1.2 ⟨p.val+j.val,by omega⟩).2,
          (ha.2.2 ⟨p.val+j.val,by omega⟩).2,hn⟩
  exact ⟨⟨fun i => ⟨(hr i).1,(hr i).2.1,(hr i).2.2.1⟩,
    fun j => ⟨(hc j).1,(hc j).2.1⟩⟩,
    fun i => (exists_nonzero_iff _).mp (hr i).2.2.2,
    fun j => ⟨(exists_nonzero_iff _).mp (hc j).2.2.2,(hc j).2.2.1⟩⟩

 theorem repairedLowerBlock_avoids312 {n : ℕ} (A : Rectangle n n)
    (hav : Avoids312 A) (p : Fin n) : Avoids312 (repairedLowerBlock A p) := by
  have hp (i j : Fin (n-p.val)) (h : repairedLowerBlock A p i j = .plus) :
      lowerBlock A p.val i j = .plus := by
    unfold repairedLowerBlock at h
    split_ifs at h with hc
    exact h
  rintro ⟨i₁,i₂,i₃,j₁,j₂,j₃,h12,h23,hj12,hj23,h13,h21,h32⟩
  exact lowerBlock_avoids312 A hav p.val
    ⟨i₁,i₂,i₃,j₁,j₂,j₃,h12,h23,hj12,hj23,hp _ _ h13,hp _ _ h21,hp _ _ h32⟩

end ASR312
