import MainTheorems.Chores.ParallelTransfer

namespace ResearchMain.Chores

variable {A E I : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

structure RotatingPairs (A E I : Type*) where
  high : I → A
  low : I → A
  highChore : I → E
  lowChore : I → E
  high_injective : Function.Injective high
  low_injective : Function.Injective low
  cross : ∀ i j, high i ≠ low j
  cycle : I ≃ I

namespace RotatingPairs

def cheapTransfers (P : RotatingPairs A E I) : PairedTransfers A E I where
  source := P.low
  target := P.high ∘ P.cycle
  chore := P.lowChore
  source_injective := P.low_injective
  target_injective := P.high_injective.comp P.cycle.injective
  cross := fun i j => (P.cross (P.cycle j) i).symm

def fillerTransfers (P : RotatingPairs A E I) : PairedTransfers A E I where
  source := P.high
  target := P.low ∘ P.cycle.symm
  chore := P.highChore
  source_injective := P.high_injective
  target_injective := P.low_injective.comp P.cycle.symm.injective
  cross := fun i j => P.cross i (P.cycle.symm j)

noncomputable def allocation (P : RotatingPairs A E I) (f : E → A) : E → A :=
  P.fillerTransfers.allocation (P.cheapTransfers.allocation f)

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem filler_owner (P : RotatingPairs A E I) {f : E → A}
    (hh : ∀ i, f (P.highChore i) = P.high i)
    (hl : ∀ i, f (P.lowChore i) = P.low i) (i : I) :
    P.cheapTransfers.allocation f (P.highChore i) = P.high i := by
  rw [P.cheapTransfers.allocation_other f]
  · exact hh i
  · intro j hij
    exact P.cross i j ((hh i).symm.trans ((congrArg f hij).trans (hl j)))

theorem high_bundle (P : RotatingPairs A E I) {f : E → A}
    (hh : ∀ i, f (P.highChore i) = P.high i)
    (hl : ∀ i, f (P.lowChore i) = P.low i) (i : I) :
    bundle (P.allocation f) (P.high i) =
      insert (P.lowChore (P.cycle.symm i)) ((bundle f (P.high i)).erase (P.highChore i)) := by
  have htarget := P.cheapTransfers.target_bundle hl (P.cycle.symm i)
  change bundle (P.cheapTransfers.allocation f) (P.high (P.cycle (P.cycle.symm i))) =
    insert (P.lowChore (P.cycle.symm i)) (bundle f (P.high (P.cycle (P.cycle.symm i)))) at htarget
  rw [Equiv.apply_symm_apply] at htarget
  have hsource : bundle (P.allocation f) (P.high i) =
      (bundle (P.cheapTransfers.allocation f) (P.high i)).erase (P.highChore i) :=
    P.fillerTransfers.source_bundle (P.filler_owner hh hl) i
  rw [hsource, htarget]
  have hne : P.lowChore (P.cycle.symm i) ≠ P.highChore i := by
    intro h
    exact P.cross i (P.cycle.symm i) ((hh i).symm.trans ((congrArg f h.symm).trans (hl _)))
  exact Finset.erase_insert_of_ne hne

theorem low_bundle (P : RotatingPairs A E I) {f : E → A}
    (hh : ∀ i, f (P.highChore i) = P.high i)
    (hl : ∀ i, f (P.lowChore i) = P.low i) (i : I) :
    bundle (P.allocation f) (P.low i) =
      insert (P.highChore (P.cycle i)) ((bundle f (P.low i)).erase (P.lowChore i)) := by
  have htarget := P.fillerTransfers.target_bundle (P.filler_owner hh hl) (P.cycle i)
  change bundle (P.allocation f) (P.low (P.cycle.symm (P.cycle i))) =
    insert (P.highChore (P.cycle i)) (bundle (P.cheapTransfers.allocation f)
      (P.low (P.cycle.symm (P.cycle i)))) at htarget
  rw [Equiv.symm_apply_apply] at htarget
  have hsource : bundle (P.cheapTransfers.allocation f) (P.low i) =
      (bundle f (P.low i)).erase (P.lowChore i) := P.cheapTransfers.source_bundle hl i
  rw [htarget, hsource]

omit [DecidableEq E] in
theorem other_bundle (P : RotatingPairs A E I) {f : E → A}
    (hh : ∀ i, f (P.highChore i) = P.high i)
    (hl : ∀ i, f (P.lowChore i) = P.low i) {a : A}
    (ha : ∀ i, a ≠ P.high i ∧ a ≠ P.low i) :
    bundle (P.allocation f) a = bundle f a := by
  rw [allocation, P.fillerTransfers.other_bundle (P.filler_owner hh hl)
    (fun i => ⟨(ha i).1, (ha (P.cycle.symm i)).2⟩)]
  exact P.cheapTransfers.other_bundle hl (fun i => ⟨(ha i).2, (ha (P.cycle i)).1⟩)

end RotatingPairs

theorem replacement_card {f g : E → A} {a : A} {e d : E}
    (he : e ∈ bundle f a) (hd : d ∉ bundle f a)
    (hg : bundle g a = insert d ((bundle f a).erase e)) :
    (bundle g a).card = (bundle f a).card := by
  rw [hg, Finset.card_insert_of_notMem (fun h => hd (Finset.mem_of_mem_erase h))]
  exact Finset.card_erase_add_one he

theorem replacement_expensive (M : TwoCheapModel A E) {f g : E → A}
    {a : A} {e d : E} (he : e ∈ bundle f a) (hd : d ∉ bundle f a)
    (hg : bundle g a = insert d ((bundle f a).erase e)) (v : A) :
    expensiveCount M g v a + (if M.Cheap v e then 0 else 1) =
      expensiveCount M f v a + (if M.Cheap v d then 0 else 1) := by
  have hd' : d ∉ ((bundle f a).filter (fun x => ¬M.Cheap v x)).erase e := by
    intro h
    exact hd (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).1
  unfold expensiveCount
  rw [hg, Finset.filter_insert, Finset.filter_erase]
  by_cases hce : M.Cheap v e <;> by_cases hcd : M.Cheap v d
  · simp [hce, hcd]
  · have hen : e ∉ (bundle f a).filter (fun x => ¬M.Cheap v x) := by simp [hce]
    simp only [hce, hcd, not_false_eq_true, ite_true, ite_false, add_zero]
    rw [Finset.erase_eq_of_notMem hen]
    exact Finset.card_insert_of_notMem (fun h => hd (Finset.mem_filter.mp h).1)
  · have he' : e ∈ (bundle f a).filter (fun x => ¬M.Cheap v x) :=
      Finset.mem_filter.mpr ⟨he, hce⟩
    simp only [hce, hcd, not_true_eq_false, ite_true, ite_false, add_zero]
    exact Finset.card_erase_add_one he'
  · have he' : e ∈ (bundle f a).filter (fun x => ¬M.Cheap v x) :=
      Finset.mem_filter.mpr ⟨he, hce⟩
    simp only [hce, hcd, not_false_eq_true, ite_true, ite_false]
    rw [Finset.card_insert_of_notMem hd']
    have h := Finset.card_erase_add_one he'
    omega

end ResearchMain.Chores
