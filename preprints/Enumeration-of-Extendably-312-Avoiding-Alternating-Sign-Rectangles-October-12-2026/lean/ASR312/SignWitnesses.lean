import ASR312.ColumnStructure

namespace ASR312

 theorem plus_before_minus {n : ℕ} (f : Fin n → Entry)
    (hs : StartsPositive (List.ofFn f)) (j : Fin n) (hj : f j = .minus) :
    ∃ i, i < j ∧ f i = .plus := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    revert hj
    refine Fin.cases ?_ (fun t => ?_) j
    · intro hj0
      have hm := startsPositive_cons_not_minus (l := List.ofFn (fun i => f i.succ))
        (by simpa only [List.ofFn_succ] using hs)
      exact False.elim (hm hj0)
    · intro hjt
      cases he : f 0 with
      | minus =>
        have hm := startsPositive_cons_not_minus (l := List.ofFn (fun i => f i.succ))
          (by simpa only [List.ofFn_succ] using hs)
        exact False.elim (hm he)
      | zero =>
        have ht : StartsPositive (List.ofFn (fun i => f i.succ)) := by
          simpa [StartsPositive,nonzeroEntries,List.ofFn_succ,he] using hs
        obtain ⟨i,hi,hp⟩ := ih (fun i => f i.succ) ht t hjt
        exact ⟨i.succ,Fin.succ_lt_succ_iff.mpr hi,hp⟩
      | plus => exact ⟨0,by simp,he⟩

 theorem reverse_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) :
    (List.ofFn f).reverse = List.ofFn (fun i => f i.rev) := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    simp only [List.getElem_reverse,List.length_ofFn,List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

 theorem plus_after_minus {n : ℕ} (f : Fin n → Entry)
    (he : EndsPositive (List.ofFn f)) (j : Fin n) (hj : f j = .minus) :
    ∃ i, j < i ∧ f i = .plus := by
  have hs : StartsPositive (List.ofFn (fun i => f i.rev)) := by
    rw [← reverse_ofFn]
    simpa only [StartsPositive,EndsPositive,nonzeroEntries,List.filter_reverse,List.head?_reverse] using he
  obtain ⟨i,hi,hp⟩ := plus_before_minus (fun i => f i.rev) hs j.rev (by simpa using hj)
  exact ⟨i.rev,(Fin.lt_rev_iff).mp hi,hp⟩

end ASR312
