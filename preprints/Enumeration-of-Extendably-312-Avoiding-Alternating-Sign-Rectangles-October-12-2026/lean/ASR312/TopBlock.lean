import ASR312.PositivePivot

namespace ASR312

 theorem nonzeroEntries_take_ofFn {n t : ℕ} (f : Fin n → Entry)
    (hz : ∀ j, t ≤ j.val → f j = .zero) :
    nonzeroEntries ((List.ofFn f).take t) = nonzeroEntries (List.ofFn f) := by
  have hd : nonzeroEntries ((List.ofFn f).drop t) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hx
    have hlt : t+j < n := by simp only [List.length_drop,List.length_ofFn] at hj; omega
    have hh := hz ⟨t+j,hlt⟩ (by simp)
    simp only [List.getElem_drop,List.getElem_ofFn] at he
    rw [← he,hh]
    simp
  have he := congrArg nonzeroEntries (List.take_append_drop t (List.ofFn f))
  simp only [nonzeroEntries,List.filter_append] at he
  change nonzeroEntries ((List.ofFn f).take t) ++ nonzeroEntries ((List.ofFn f).drop t) = nonzeroEntries (List.ofFn f) at he
  simpa only [hd,List.append_nil] using he

 def topBlock {n : ℕ} (A : Rectangle (n+1) (n+1)) (p : Fin (n+1)) : Rectangle p.val p.val :=
  fun i j => A ⟨i.val,by omega⟩ ⟨j.val+1,by omega⟩

 theorem topBlock_row_entries {n : ℕ} (A : Rectangle (n+1) (n+1))
    (p : Fin (n+1)) (hz : ∀ q b, q < p → p < b → A q b = .zero)
    (hfirst : ∀ q, q < p → A q 0 = .zero) (i : Fin p.val) :
    nonzeroEntries (row (topBlock A p) i) =
      nonzeroEntries (row A ⟨i.val,by omega⟩) := by
  let q : Fin (n+1) := ⟨i.val,by omega⟩
  have hq : q < p := i.isLt
  have he := nonzeroEntries_take_ofFn (A q) (t:=p.val+1) (fun b hb => hz q b hq (by exact hb))
  rw [take_ofFn (by omega : p.val+1 ≤ n+1),List.ofFn_succ] at he
  have hzero : A q (Fin.castLE (by omega : p.val+1 ≤ n+1) 0) = .zero := by
    have hh : Fin.castLE (by omega : p.val+1 ≤ n+1) (0 : Fin (p.val+1)) = (0 : Fin (n+1)) := Fin.ext rfl
    rw [hh]
    exact hfirst q hq
  simp only [hzero,nonzeroEntries,List.filter_cons] at he
  exact he

 theorem topBlock_col {n : ℕ} (A : Rectangle (n+1) (n+1)) (p : Fin (n+1)) (j : Fin p.val) :
    col (topBlock A p) j = (col A ⟨j.val+1,by omega⟩).take p.val := by
  simp only [col]
  rw [take_ofFn (by omega : p.val ≤ n+1)]
  rfl

 theorem topBlock_asm {n : ℕ} (A : Rectangle (n+1) (n+1)) (ha : IsASM A)
    (p : Fin (n+1)) (hz : ∀ q b, q < p → p < b → A q b = .zero)
    (hfirst : ∀ q, q < p → A q 0 = .zero)
    (hc : ∀ b : Fin (n+1), 0 < b → b ≤ p → prefixSum (fun q => A q b) p.val = 1) :
    IsASM (topBlock A p) := by
  have hcol (j : Fin p.val) : Alternates (col (topBlock A p) j) ∧
      StartsPositive (col (topBlock A p) j) := by
    rw [topBlock_col]
    exact ⟨alternates_prefix (List.take_prefix _ _) (ha.1.2 _).1,
      startsPositive_prefix (List.take_prefix _ _) (ha.1.2 _).2⟩
  have hcolsum (j : Fin p.val) : entrySum (col (topBlock A p) j) = 1 := by
    rw [topBlock_col]
    exact (prefixSum_eq (fun q => A q ⟨j.val+1,by omega⟩) (by omega)).symm.trans
      (hc ⟨j.val+1,by omega⟩ (by change 0 < j.val+1; omega) (by change j.val+1 ≤ p.val; omega))
  refine ⟨⟨?_,hcol⟩,?_,?_⟩
  · intro i
    have he := topBlock_row_entries A p hz hfirst i
    simpa only [Alternates,StartsPositive,EndsPositive,he] using ha.1.1 ⟨i.val,by omega⟩
  · intro i
    have he := topBlock_row_entries A p hz hfirst i
    have hn : nonzeroEntries (row (topBlock A p) i) ≠ [] := by
      rw [he]
      intro hnil
      have hall := (row_nonzeroEntries_empty_iff A ⟨i.val,by omega⟩).mp hnil
      obtain ⟨j,hj⟩ := ha.2.1 ⟨i.val,by omega⟩
      exact hj (hall j)
    by_contra hh
    have hall : ∀ j, topBlock A p i j = .zero := by simpa using hh
    exact hn ((row_nonzeroEntries_empty_iff _ _).mpr hall)
  · intro j
    have hh := column_sum_one_properties _ (hcol j).1 (hcol j).2 (hcolsum j)
    refine ⟨?_,hh.2⟩
    by_contra hn
    have hall : ∀ i, topBlock A p i j = .zero := by simpa using hn
    have he : col (topBlock A p) j = List.ofFn (fun _ : Fin p.val => Entry.zero) := by
      unfold col
      congr 1
      funext i
      exact hall i
    apply hh.1
    rw [he]
    exact nonzero_ofFn_zero _

 theorem topBlock_avoids312 {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : Avoids312 A) (p : Fin (n+1)) : Avoids312 (topBlock A p) := by
  rintro ⟨i₁,i₂,i₃,j₁,j₂,j₃,h12,h23,hj12,hj23,h13,h21,h32⟩
  apply ha
  refine ⟨⟨i₁.val,by omega⟩,⟨i₂.val,by omega⟩,⟨i₃.val,by omega⟩,
    ⟨j₁.val+1,by omega⟩,⟨j₂.val+1,by omega⟩,⟨j₃.val+1,by omega⟩,h12,h23,?_,?_,h13,h21,h32⟩
  · change j₁.val+1 < j₂.val+1
    exact Nat.add_lt_add_right hj12 1
  · change j₂.val+1 < j₃.val+1
    exact Nat.add_lt_add_right hj23 1

end ASR312
