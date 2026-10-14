import MainTheorems.PreorderGamma.RootPolytope

namespace ResearchMain.PreorderGamma

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

structure RootSupportingData (E : Type*) [Preorder E] where
  left : Option E → ℝ
  right : Option E → ℝ
  maximum : ℝ
  bound : ∀ i j, augmentedRelation i j → left i + right j ≤ maximum

noncomputable def tightEdges (d : RootSupportingData E) : Finset (AugmentedEdge E) := by
  classical
  exact Finset.univ.filter fun e => d.left e.val.1 + d.right e.val.2 = d.maximum

omit [DecidableEq E] in
@[simp] theorem mem_tightEdges (d : RootSupportingData E) (e : AugmentedEdge E) :
    e ∈ tightEdges d ↔ d.left e.val.1 + d.right e.val.2 = d.maximum := by
  classical
  simp [tightEdges]

def IsRootFacet (d : RootSupportingData E) : Prop :=
  (tightEdges d).Nonempty ∧ tightEdges d ≠ Finset.univ ∧
    ∀ d' : RootSupportingData E, tightEdges d ⊆ tightEdges d' →
      tightEdges d' ≠ Finset.univ → tightEdges d = tightEdges d'

def diagonalEdge (i : Option E) : AugmentedEdge E :=
  ⟨(i, i), by cases i <;> simp [augmentedRelation]⟩

omit [Fintype E] [DecidableEq E] in
theorem augmentedRelation_some_trans {i j : Option E} {a : E}
    (hi : augmentedRelation i (some a)) (hj : augmentedRelation (some a) j) :
    augmentedRelation i j := by
  cases i <;> cases j <;> simp_all [augmentedRelation]
  exact le_trans hj hi

noncomputable def leftCoordinateSupport (a : E) : RootSupportingData E where
  left := fun i => if i = some a then -1 else 0
  right := fun _ => 0
  maximum := 0
  bound := by intro i j h; split_ifs <;> norm_num

noncomputable def rightCoordinateSupport (a : E) : RootSupportingData E where
  left := fun _ => 0
  right := fun i => if i = some a then -1 else 0
  maximum := 0
  bound := by intro i j h; split_ifs <;> norm_num

@[simp] theorem mem_leftCoordinateSupport (a : E) (e : AugmentedEdge E) :
    e ∈ tightEdges (leftCoordinateSupport a) ↔ e.val.1 ≠ some a := by
  rw [mem_tightEdges]
  by_cases h : e.val.1 = some a <;> simp [leftCoordinateSupport, h]

@[simp] theorem mem_rightCoordinateSupport (a : E) (e : AugmentedEdge E) :
    e ∈ tightEdges (rightCoordinateSupport a) ↔ e.val.2 ≠ some a := by
  rw [mem_tightEdges]
  by_cases h : e.val.2 = some a <;> simp [rightCoordinateSupport, h]

theorem leftCoordinateSupport_proper (a : E) :
    tightEdges (leftCoordinateSupport a) ≠ Finset.univ := by
  intro h
  have hm : diagonalEdge (some a) ∈ tightEdges (leftCoordinateSupport a) := by
    rw [h]
    exact Finset.mem_univ _
  exact (mem_leftCoordinateSupport a (diagonalEdge (some a))).mp hm rfl

theorem rightCoordinateSupport_proper (a : E) :
    tightEdges (rightCoordinateSupport a) ≠ Finset.univ := by
  intro h
  have hm : diagonalEdge (some a) ∈ tightEdges (rightCoordinateSupport a) := by
    rw [h]
    exact Finset.mem_univ _
  exact (mem_rightCoordinateSupport a (diagonalEdge (some a))).mp hm rfl

theorem missing_diagonal_isolates_side (d : RootSupportingData E) (a : E)
    (ha : diagonalEdge (some a) ∉ tightEdges d) :
    tightEdges d ⊆ tightEdges (leftCoordinateSupport a) ∨
      tightEdges d ⊆ tightEdges (rightCoordinateSupport a) := by
  classical
  have hdiag : d.left (some a) + d.right (some a) < d.maximum := by
    have hb := d.bound (some a) (some a) (le_refl a)
    have hn : d.left (some a) + d.right (some a) ≠ d.maximum := by
      intro heq
      apply ha
      exact (mem_tightEdges d (diagonalEdge (some a))).mpr heq
    exact lt_of_le_of_ne hb hn
  by_cases hex : ∃ e ∈ tightEdges d, e.val.1 = some a
  · right
    obtain ⟨e, he, hei⟩ := hex
    intro f hf
    apply (mem_rightCoordinateSupport a f).mpr
    intro hfi
    have heq := (mem_tightEdges d e).mp he
    have hfq := (mem_tightEdges d f).mp hf
    have hleft : augmentedRelation (some a) e.val.2 := hei ▸ e.property
    have hright : augmentedRelation f.val.1 (some a) := hfi ▸ f.property
    have hc := d.bound f.val.1 e.val.2 (augmentedRelation_some_trans hright hleft)
    rw [hei] at heq
    rw [hfi] at hfq
    linarith
  · left
    intro e he
    exact (mem_leftCoordinateSupport a e).mpr fun h => hex ⟨e, he, h⟩

theorem facet_missing_some_unique (d : RootSupportingData E) (hd : IsRootFacet d)
    (a : E) (ha : diagonalEdge (some a) ∉ tightEdges d) :
    ∀ i : Option E, diagonalEdge i ∉ tightEdges d ↔ i = some a := by
  have h := missing_diagonal_isolates_side d a ha
  rcases h with hl | hr
  · have heq := hd.2.2 (leftCoordinateSupport a) hl (leftCoordinateSupport_proper a)
    intro i
    rw [heq, mem_leftCoordinateSupport]
    simp [diagonalEdge]
  · have heq := hd.2.2 (rightCoordinateSupport a) hr (rightCoordinateSupport_proper a)
    intro i
    rw [heq, mem_rightCoordinateSupport]
    simp [diagonalEdge]

omit [DecidableEq E] in
theorem all_diagonals_tight (d : RootSupportingData E)
    (h : ∀ i : Option E, diagonalEdge i ∈ tightEdges d) :
    tightEdges d = Finset.univ := by
  have hdiag : ∀ i, d.left i + d.right i = d.maximum :=
    fun i => (mem_tightEdges d (diagonalEdge i)).mp (h i)
  have hleft : ∀ i, d.left i = d.left none := by
    intro i
    have h1 := d.bound i none (by cases i <;> trivial)
    have h2 := d.bound none i trivial
    have h3 := hdiag i
    have h4 := hdiag none
    linarith
  apply Finset.eq_univ_of_forall
  intro e
  apply (mem_tightEdges d e).mpr
  have h1 := hdiag e.val.2
  rw [hleft e.val.1]
  simpa only [hleft e.val.2] using h1

theorem rootFacet_unique_missing_diagonal (d : RootSupportingData E) (hd : IsRootFacet d) :
    ∃! i : Option E, diagonalEdge i ∉ tightEdges d := by
  classical
  have hex : ∃ i : Option E, diagonalEdge i ∉ tightEdges d := by
    by_contra hn
    have hall : ∀ i : Option E, diagonalEdge i ∈ tightEdges d := by
      simpa only [not_exists, not_not] using hn
    exact hd.2.1 (all_diagonals_tight d hall)
  obtain ⟨i, hi⟩ := hex
  cases i with
  | some a =>
    exact ⟨some a, hi, fun j hj => (facet_missing_some_unique d hd a hi j).mp hj⟩
  | none =>
    refine ⟨none, hi, ?_⟩
    intro j hj
    cases j with
    | none => rfl
    | some a =>
      have hfalse := (facet_missing_some_unique d hd a hj none).mp hi
      cases hfalse

end ResearchMain.PreorderGamma
