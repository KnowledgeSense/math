import ASR312.NegativeGlue

namespace ASR312

 theorem append_minus_plus_chain (L : List Entry) (hc : L.IsChain (· ≠ ·))
    (he : L.getLast? = none ∨ L.getLast? = some .plus) :
    (L ++ [Entry.minus,Entry.plus]).IsChain (· ≠ ·) := by
  apply hc.append (by simp)
  intro x hx y hy
  simp only [List.head?_cons,Option.mem_def,Option.some.injEq] at hy
  subst y
  rcases he with he | he
  · simp [he] at hx
  · have hx : Entry.plus = x := by simpa [he] using hx
    subst x
    decide

 theorem negativeGlue_asm {a b : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (b+1) (b+1)) (ha : IsASM A) (hb : IsASM B) (hz : B 0 0 = .zero) :
    IsASM (negativeGlue A B) := by
  have hr (i) : Alternates (row (negativeGlue A B) i) ∧
      StartsPositive (row (negativeGlue A B) i) ∧ EndsPositive (row (negativeGlue A B) i) ∧
      nonzeroEntries (row (negativeGlue A B) i) ≠ [] := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have hn := (exists_nonzero_iff _).mpr (ha.2.1 i)
      simpa only [Alternates,StartsPositive,EndsPositive,negativeGlue_row_top] using
        ⟨(ha.1.1 i).1,(ha.1.1 i).2.1,(ha.1.1 i).2.2,hn⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simp [Alternates,StartsPositive,EndsPositive,negativeGlue_row_pivot A B hb hz]
      · have hn := (exists_nonzero_iff _).mpr (hb.2.1 i.succ)
        simpa only [Alternates,StartsPositive,EndsPositive,negativeGlue_row_bottom] using
          ⟨(hb.1.1 i.succ).1,(hb.1.1 i.succ).2.1,(hb.1.1 i.succ).2.2,hn⟩
  have hc (j) : Alternates (col (negativeGlue A B) j) ∧
      StartsPositive (col (negativeGlue A B) j) ∧ EndsPositive (col (negativeGlue A B) j) ∧
      nonzeroEntries (col (negativeGlue A B) j) ≠ [] := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [Alternates,StartsPositive,EndsPositive,negativeGlue_col_zero]
      · have hn := (exists_nonzero_iff _).mpr (ha.2.2 j.castSucc).1
        simpa only [Alternates,StartsPositive,EndsPositive,negativeGlue_col_left] using
          ⟨(ha.1.2 j.castSucc).1,(ha.1.2 j.castSucc).2,(ha.2.2 j.castSucc).2,hn⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Alternates,StartsPositive,EndsPositive,negativeGlue_col_overlap A B hb hz]
        refine ⟨append_minus_plus_chain _ (ha.1.2 (Fin.last a)).1 (ha.2.2 (Fin.last a)).2,?_,?_,?_⟩
        · have hn := (exists_nonzero_iff _).mpr (ha.2.2 (Fin.last a)).1
          change nonzeroEntries (col A (Fin.last a)) ≠ [] at hn
          rw [List.head?_append_of_ne_nil _ hn]
          exact (ha.1.2 (Fin.last a)).2
        · simp [List.getLast?_append]
        · simp
      · have hn := (exists_nonzero_iff _).mpr (hb.2.2 j.succ).1
        simpa only [Alternates,StartsPositive,EndsPositive,negativeGlue_col_right] using
          ⟨(hb.1.2 j.succ).1,(hb.1.2 j.succ).2,(hb.2.2 j.succ).2,hn⟩
  exact ⟨⟨fun i => ⟨(hr i).1,(hr i).2.1,(hr i).2.2.1⟩,
    fun j => ⟨(hc j).1,(hc j).2.1⟩⟩,
    fun i => (exists_nonzero_iff _).mp (hr i).2.2.2,
    fun j => ⟨(exists_nonzero_iff _).mp (hc j).2.2.2,(hc j).2.2.1⟩⟩

end ASR312
