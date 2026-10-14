import Dowling.GainPartitionFilters

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem exists_impose_joint (p : GainPartition G n) (i : Fin n) :
    ∃ q : GainPartition G n, q.solutionSet = {x ∈ p.solutionSet | x i = none} ∧
      (q = p ∨ q.roots.card + 1 = p.roots.card) := by
  cases hi : p.code i with
  | none =>
    refine ⟨p, ?_, Or.inl rfl⟩
    ext x
    exact ⟨fun hx => ⟨hx, ((p.mem_solutionSet x).mp hx).1 i hi⟩, And.left⟩
  | some v =>
    rcases v with ⟨r,a⟩
    have hr : p.IsRoot r := p.rooted i r a hi
    refine ⟨p.eraseBlock r, ?_, Or.inr (p.eraseBlock_roots_card r hr)⟩
    rw [filter_joint p i r a hi, eraseBlock_solutionSet p r hr]

theorem exists_impose_link (p : GainPartition G n) (i j : Fin n) (g : G) :
    ∃ q : GainPartition G n,
      q.solutionSet = {x ∈ p.solutionSet | x j = gainAct G (x i) g} ∧
      (q = p ∨ q.roots.card + 1 = p.roots.card) := by
  cases hi : p.code i with
  | none =>
    cases hj : p.code j with
    | none =>
      refine ⟨p, ?_, Or.inl rfl⟩
      ext x
      constructor
      · intro hx
        refine ⟨hx, ?_⟩
        have hz := ((p.mem_solutionSet x).mp hx).1
        rw [hz i hi, hz j hj, gainAct_none]
      · exact And.left
    | some v =>
      rcases v with ⟨s,b⟩
      have hs : p.IsRoot s := p.rooted j s b hj
      refine ⟨p.eraseBlock s, ?_, Or.inr (p.eraseBlock_roots_card s hs)⟩
      rw [filter_link_zero_tail p i j s b g hi hj, eraseBlock_solutionSet p s hs]
  | some v =>
    rcases v with ⟨r,a⟩
    have hr : p.IsRoot r := p.rooted i r a hi
    cases hj : p.code j with
    | none =>
      refine ⟨p.eraseBlock r, ?_, Or.inr (p.eraseBlock_roots_card r hr)⟩
      rw [filter_link_zero_head p i j r a g hi hj, eraseBlock_solutionSet p r hr]
    | some v =>
      rcases v with ⟨s,b⟩
      have hs : p.IsRoot s := p.rooted j s b hj
      have hf := filter_link_nonzero p i j r s a b g hi hj
      rw [hf]
      rcases lt_trichotomy r s with hrs | hrs | hsr
      · refine ⟨p.mergeBlocks r s (a*g*b⁻¹) hr hrs, ?_,
          Or.inr (p.mergeBlocks_roots_card r s _ hr hs hrs)⟩
        exact p.mergeBlocks_solutionSet r s _ hr hs hrs
      · subst s
        by_cases hh : a*g*b⁻¹ = 1
        · refine ⟨p, ?_, Or.inl rfl⟩
          simp [hh, gainAct_one]
        · refine ⟨p.eraseBlock r, ?_, Or.inr (p.eraseBlock_roots_card r hr)⟩
          rw [filter_same_root p r _ hh, eraseBlock_solutionSet p r hr]
      · refine ⟨p.mergeBlocks s r (a*g*b⁻¹)⁻¹ hs hsr, ?_,
          Or.inr (p.mergeBlocks_roots_card s r _ hs hr hsr)⟩
        rw [filter_reverse_roots p r s]
        exact p.mergeBlocks_solutionSet s r _ hs hr hsr

/-- Every actual joint or link either is redundant or removes exactly one free block. -/
theorem exists_impose_edge (p : GainPartition G n) (e : Edge G n) :
    ∃ q : GainPartition G n,
      q.solutionSet = {x ∈ p.solutionSet | Satisfies G n x e} ∧
      (q = p ∨ q.roots.card + 1 = p.roots.card) := by
  cases e with
  | inl i => exact p.exists_impose_joint i
  | inr e => exact p.exists_impose_link e.tail e.head e.gain

end Dowling.GainPartition
