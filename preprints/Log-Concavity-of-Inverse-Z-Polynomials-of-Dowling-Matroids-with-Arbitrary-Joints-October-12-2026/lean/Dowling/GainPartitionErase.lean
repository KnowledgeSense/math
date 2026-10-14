import Dowling.GainPartitionEquations

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

/-- Pin one free potential block to zero. -/
def eraseBlock (p : GainPartition G n) (r : Fin n) : GainPartition G n where
  code i := match p.code i with
    | none => none
    | some (s,g) => if s = r then none else some (s,g)
  rooted := by
    intro i j g h
    cases hi : p.code i with
    | none => simp [hi] at h
    | some v =>
      rcases v with ⟨s,a⟩
      by_cases hs : s = r
      · simp [hi, hs] at h
      · simp only [hi, hs, ite_false, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        simp [p.rooted i s a hi, hs]
  least := by
    intro i j g h
    cases hi : p.code i with
    | none => simp [hi] at h
    | some v =>
      rcases v with ⟨s,a⟩
      by_cases hs : s = r
      · simp [hi, hs] at h
      · simp only [hi, hs, ite_false, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact p.least i s a hi

theorem eraseBlock_assignment (p : GainPartition G n) (r : Fin n) (a : Fin n → Option G) :
    (p.eraseBlock r).assignment a = p.assignment (Function.update a r none) := by
  funext i
  cases hi : p.code i with
  | none => simp [assignment, eraseBlock, hi]
  | some v =>
    rcases v with ⟨s,g⟩
    by_cases hs : s = r
    · subst s
      simp [assignment, eraseBlock, hi]
    · simp [assignment, eraseBlock, hi, hs]

/-- The update is exactly intersection with the joint equation on this root. -/
theorem eraseBlock_solutionSet (p : GainPartition G n) (r : Fin n) (hr : p.IsRoot r) :
    (p.eraseBlock r).solutionSet = {x ∈ p.solutionSet | x r = none} := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    rw [eraseBlock_assignment]
    exact ⟨p.assignment_mem _, by rw [p.assignment_root _ r hr]; simp⟩
  · rintro ⟨⟨a,rfl⟩, ha⟩
    rw [p.assignment_root a r hr] at ha
    refine ⟨a, ?_⟩
    rw [eraseBlock_assignment]
    congr 1
    funext j
    by_cases hj : j = r
    · subst j
      simp [ha]
    · simp [Function.update_of_ne hj]

theorem eraseBlock_isRoot (p : GainPartition G n) (r j : Fin n) :
    (p.eraseBlock r).IsRoot j ↔ p.IsRoot j ∧ j ≠ r := by
  cases hj : p.code j with
  | none => simp [IsRoot, eraseBlock, hj]
  | some v =>
    rcases v with ⟨s,g⟩
    by_cases hs : s = r
    · subst s
      simp [IsRoot, eraseBlock, hj, Prod.mk.injEq]
      exact fun hrj _ => hrj.symm
    · simp only [IsRoot, eraseBlock, hj, hs, ite_false, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl,rfl⟩
        exact ⟨⟨rfl,rfl⟩,hs⟩
      · exact fun h => h.1

theorem eraseBlock_roots (p : GainPartition G n) (r : Fin n) :
    (p.eraseBlock r).roots = p.roots.erase r := by
  ext j
  simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
    eraseBlock_isRoot, and_comm]

theorem eraseBlock_roots_card (p : GainPartition G n) (r : Fin n) (hr : p.IsRoot r) :
    (p.eraseBlock r).roots.card + 1 = p.roots.card := by
  rw [eraseBlock_roots]
  exact Finset.card_erase_add_one (by simpa [roots] using hr)

end Dowling.GainPartition
