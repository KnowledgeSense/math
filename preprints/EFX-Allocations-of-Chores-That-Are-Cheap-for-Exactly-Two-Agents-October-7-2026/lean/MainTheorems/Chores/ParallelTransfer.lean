import MainTheorems.Chores.Transfer

namespace ResearchMain.Chores

variable {A E I : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

structure PairedTransfers (A E I : Type*) where
  source : I → A
  target : I → A
  chore : I → E
  source_injective : Function.Injective source
  target_injective : Function.Injective target
  cross : ∀ i j, source i ≠ target j

namespace PairedTransfers

noncomputable def allocation (P : PairedTransfers A E I) (f : E → A) : E → A := by
  classical
  exact fun e => if h : ∃ i, P.chore i = e then P.target (Classical.choose h) else f e

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem chore_injective (P : PairedTransfers A E I) {f : E → A}
    (hf : ∀ i, f (P.chore i) = P.source i) : Function.Injective P.chore := by
  intro i j hij
  apply P.source_injective
  rw [← hf i, ← hf j, hij]

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem allocation_chore (P : PairedTransfers A E I) {f : E → A}
    (hf : ∀ i, f (P.chore i) = P.source i) (i : I) :
    P.allocation f (P.chore i) = P.target i := by
  classical
  unfold allocation
  rw [dite_eq_left ⟨i, rfl⟩]
  congr 1
  exact P.chore_injective hf (Classical.choose_spec (show ∃ j, P.chore j = P.chore i from ⟨i, rfl⟩))

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem allocation_other (P : PairedTransfers A E I) (f : E → A) {e : E}
    (he : ∀ i, e ≠ P.chore i) : P.allocation f e = f e := by
  classical
  unfold allocation
  apply dite_eq_right
  rintro ⟨i, hi⟩
  exact he i hi.symm

theorem source_bundle (P : PairedTransfers A E I) {f : E → A}
    (hf : ∀ i, f (P.chore i) = P.source i) (i : I) :
    bundle (P.allocation f) (P.source i) = (bundle f (P.source i)).erase (P.chore i) := by
  classical
  ext e
  simp only [mem_bundle, Finset.mem_erase]
  by_cases he : ∃ j, P.chore j = e
  · obtain ⟨j, rfl⟩ := he
    rw [P.allocation_chore hf, hf j]
    have hc := P.cross i j
    constructor
    · intro h
      exact False.elim (hc h.symm)
    · rintro ⟨hne, hsource⟩
      exact False.elim (hne (congrArg P.chore (P.source_injective hsource)))
  · rw [P.allocation_other f (by simpa [eq_comm] using he)]
    have hne : e ≠ P.chore i := by
      intro h
      exact he ⟨i, h.symm⟩
    simp [hne]

theorem target_bundle (P : PairedTransfers A E I) {f : E → A}
    (hf : ∀ i, f (P.chore i) = P.source i) (i : I) :
    bundle (P.allocation f) (P.target i) = insert (P.chore i) (bundle f (P.target i)) := by
  classical
  ext e
  simp only [mem_bundle, Finset.mem_insert]
  by_cases he : ∃ j, P.chore j = e
  · obtain ⟨j, rfl⟩ := he
    rw [P.allocation_chore hf, hf j]
    have hc := P.cross j i
    constructor
    · intro h
      exact Or.inl (congrArg P.chore (P.target_injective h))
    · rintro (h | h)
      · exact congrArg P.target (P.chore_injective hf h)
      · exact False.elim (hc h)
  · rw [P.allocation_other f (by simpa [eq_comm] using he)]
    have hne : e ≠ P.chore i := by
      intro h
      exact he ⟨i, h.symm⟩
    simp [hne]

omit [DecidableEq E] in
theorem other_bundle (P : PairedTransfers A E I) {f : E → A}
    (hf : ∀ i, f (P.chore i) = P.source i) {a : A}
    (ha : ∀ i, a ≠ P.source i ∧ a ≠ P.target i) :
    bundle (P.allocation f) a = bundle f a := by
  classical
  ext e
  simp only [mem_bundle]
  by_cases he : ∃ j, P.chore j = e
  · obtain ⟨j, rfl⟩ := he
    rw [P.allocation_chore hf, hf j]
    simp [(ha j).1.symm, (ha j).2.symm]
  · rw [P.allocation_other f (by simpa [eq_comm] using he)]

omit [Fintype E] [DecidableEq E] in
theorem separated (P : PairedTransfers A E I) (M : TwoCheapModel A E)
    {S : Finset A} {f : E → A} (hf : Separated M S f)
    (ht : ∀ i, P.target i ∈ S) (hc : ∀ i, M.Cheap (P.target i) (P.chore i)) :
    Separated M S (P.allocation f) := by
  classical
  intro e
  unfold allocation
  split_ifs with h
  · let i := Classical.choose h
    have hi : P.chore i = e := Classical.choose_spec h
    have hcheap : M.Cheap (P.target i) e := by simpa only [← hi] using hc i
    have htouch : M.first e ∈ S ∨ M.second e ∈ S := by
      rcases hcheap with h | h
      · exact Or.inl (h ▸ ht i)
      · exact Or.inr (h ▸ ht i)
    rw [separatedAllowed, ite_eq_left htouch, Finset.mem_inter, mem_endpointAllowed]
    exact ⟨hcheap, ht i⟩
  · exact hf e

end PairedTransfers

end ResearchMain.Chores
