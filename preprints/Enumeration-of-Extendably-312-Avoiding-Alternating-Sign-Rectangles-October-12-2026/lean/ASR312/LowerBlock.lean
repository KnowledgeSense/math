import ASR312.LowerZeros

namespace ASR312

 theorem nonzeroEntries_drop_ofFn {n t : ℕ} (f : Fin n → Entry)
    (hz : ∀ j, j.val < t → f j = .zero) :
    nonzeroEntries ((List.ofFn f).drop t) = nonzeroEntries (List.ofFn f) := by
  have hd : nonzeroEntries ((List.ofFn f).take t) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hx
    have hlt : j < n := by simp only [List.length_take,List.length_ofFn] at hj; omega
    have hjt : j < t := by simp only [List.length_take,List.length_ofFn] at hj; omega
    have hh := hz ⟨j,hlt⟩ hjt
    simp only [List.getElem_take,List.getElem_ofFn] at he
    rw [← he,hh]
    simp
  have he := congrArg nonzeroEntries (List.take_append_drop t (List.ofFn f))
  simp only [nonzeroEntries,List.filter_append] at he
  change nonzeroEntries ((List.ofFn f).take t) ++ nonzeroEntries ((List.ofFn f).drop t) =
    nonzeroEntries (List.ofFn f) at he
  simpa only [hd,List.nil_append] using he

 theorem drop_ofFn {α : Type*} {n : ℕ} (t : ℕ) (f : Fin n → α) :
    (List.ofFn f).drop t = List.ofFn (fun i : Fin (n-t) => f ⟨t+i.val,by omega⟩) := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    simp only [List.getElem_drop,List.getElem_ofFn]

 def lowerBlock {n : ℕ} (A : Rectangle n n) (t : ℕ) : Rectangle (n-t) (n-t) :=
  fun i j => A ⟨t+i.val,by omega⟩ ⟨t+j.val,by omega⟩

 theorem lowerBlock_row {n : ℕ} (A : Rectangle n n) (t : ℕ) (i : Fin (n-t)) :
    row (lowerBlock A t) i = (row A ⟨t+i.val,by omega⟩).drop t := by
  simp only [row,drop_ofFn]
  rfl

 theorem lowerBlock_col {n : ℕ} (A : Rectangle n n) (t : ℕ) (j : Fin (n-t)) :
    col (lowerBlock A t) j = (col A ⟨t+j.val,by omega⟩).drop t := by
  simp only [col,drop_ofFn]
  rfl

 theorem lowerBlock_asm {n : ℕ} (A : Rectangle n n) (ha : IsASM A) (t : ℕ)
    (hl : ∀ i j : Fin n, t ≤ i.val → j.val < t → A i j = .zero)
    (hu : ∀ i j : Fin n, i.val < t → t ≤ j.val → A i j = .zero) : IsASM (lowerBlock A t) := by
  have hrow (i : Fin (n-t)) : nonzeroEntries (row (lowerBlock A t) i) =
      nonzeroEntries (row A ⟨t+i.val,by omega⟩) := by
    rw [lowerBlock_row]
    exact nonzeroEntries_drop_ofFn _ (fun j hj => hl _ j (by simp) hj)
  have hcol (j : Fin (n-t)) : nonzeroEntries (col (lowerBlock A t) j) =
      nonzeroEntries (col A ⟨t+j.val,by omega⟩) := by
    rw [lowerBlock_col]
    exact nonzeroEntries_drop_ofFn _ (fun i hi => hu i _ hi (by simp))
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro i
    simpa only [Alternates,StartsPositive,EndsPositive,hrow] using ha.1.1 ⟨t+i.val,by omega⟩
  · intro j
    simpa only [Alternates,StartsPositive,hcol] using ha.1.2 ⟨t+j.val,by omega⟩
  · intro i
    by_contra hh
    have hall : ∀ j, lowerBlock A t i j = .zero := by simpa using hh
    have he := (row_nonzeroEntries_empty_iff _ _).mpr hall
    rw [hrow] at he
    have hall' := (row_nonzeroEntries_empty_iff _ _).mp he
    obtain ⟨j,hj⟩ := ha.2.1 ⟨t+i.val,by omega⟩
    exact hj (hall' j)
  · intro j
    refine ⟨?_,?_⟩
    · by_contra hh
      have hall : ∀ i, lowerBlock A t i j = .zero := by simpa using hh
      have he : nonzeroEntries (col (lowerBlock A t) j) = [] := by
        have hc : col (lowerBlock A t) j = List.ofFn (fun _ : Fin (n-t) => Entry.zero) := by
          unfold col
          congr 1
          funext i
          exact hall i
        rw [hc]
        exact nonzero_ofFn_zero _
      rw [hcol] at he
      have hall' : ∀ i, A i ⟨t+j.val,by omega⟩ = .zero := by
        simpa [nonzeroEntries,col,List.filter_eq_nil_iff] using he
      obtain ⟨i,hi⟩ := (ha.2.2 ⟨t+j.val,by omega⟩).1
      exact hi (hall' i)
    · simpa only [EndsPositive,hcol] using (ha.2.2 ⟨t+j.val,by omega⟩).2

 theorem lowerBlock_avoids312 {n : ℕ} (A : Rectangle n n) (ha : Avoids312 A) (t : ℕ) :
    Avoids312 (lowerBlock A t) := by
  rintro ⟨i₁,i₂,i₃,j₁,j₂,j₃,h12,h23,hj12,hj23,h13,h21,h32⟩
  apply ha
  refine ⟨⟨t+i₁.val,by omega⟩,⟨t+i₂.val,by omega⟩,⟨t+i₃.val,by omega⟩,
    ⟨t+j₁.val,by omega⟩,⟨t+j₂.val,by omega⟩,⟨t+j₃.val,by omega⟩,?_,?_,?_,?_,h13,h21,h32⟩
  · exact Nat.add_lt_add_left h12 t
  · exact Nat.add_lt_add_left h23 t
  · exact Nat.add_lt_add_left hj12 t
  · exact Nat.add_lt_add_left hj23 t

 theorem asm_pure_lowerBlock {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin (n+1)) (hp : A p 0 = .plus)
    (hpure : ∀ b, b ≠ 0 → A p b = .zero) :
    IsASM (lowerBlock A (p.val+1)) ∧ Avoids312 (lowerBlock A (p.val+1)) := by
  refine ⟨lowerBlock_asm A ha (p.val+1) ?_ ?_,lowerBlock_avoids312 A hav _⟩
  · intro i j hi hj
    have hpi : p < i := hi
    have hjp : j ≤ p := by change j.val ≤ p.val; omega
    rcases lt_or_eq_of_le hjp with hjp | rfl
    · exact asm_below_left_zero A ha hav p hp i j hpi hjp
    · exact asm_pure_pivot_lower_zero A ha hav j hp hpure i hpi
  · intro i j hi hj
    have hpj : p < j := hj
    have hip : i ≤ p := by change i.val ≤ p.val; omega
    rcases lt_or_eq_of_le hip with hip | rfl
    · exact (asm_pivot_top_facts A ha hav p hp).1 i j hip hpj
    · exact hpure j (ne_of_gt (lt_of_le_of_lt (Fin.zero_le i) hpj))

end ASR312
