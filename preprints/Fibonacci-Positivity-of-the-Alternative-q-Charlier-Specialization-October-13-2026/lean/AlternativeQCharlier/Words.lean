import AlternativeQCharlier.Definitions

namespace AlternativeQCharlier

@[simp] theorem Word.toList_addOne (w : Word) :
    w.addOne.toList = false :: w.toList := by
  cases w <;> simp [Word.addOne, Word.toList, List.replicate_succ, List.cons_append]

@[simp] theorem Word.toList_fromList (l : List Bool) :
    (Word.fromList l).toList = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b <;> simp [Word.fromList, Word.toList, ih]

/-- Every finite word in the source alphabet is represented. -/
theorem Word.toList_surjective : Function.Surjective Word.toList := by
  intro l
  exact ⟨Word.fromList l, Word.toList_fromList l⟩

end AlternativeQCharlier
