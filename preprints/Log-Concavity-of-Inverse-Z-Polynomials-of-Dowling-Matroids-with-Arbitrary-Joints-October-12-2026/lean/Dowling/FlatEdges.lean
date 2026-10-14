import Dowling.AdmissiblePartitions

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

/-- Exactly the available joints and links implied by the potential blocks. -/
def flatEdges (X : Set (Fin n)) (p : GainPartition G n) : Set (Edge G n) :=
  {e | e ∈ ground G n X ∧ ∀ x ∈ p.solutionSet, Satisfies G n x e}

theorem flatEdges_subset_ground (X : Set (Fin n)) (p : GainPartition G n) :
    flatEdges X p ⊆ ground G n X := fun _ h => h.1

theorem flatEdges_joint (X : Set (Fin n)) (p : GainPartition G n) (i : Fin n) :
    Sum.inl i ∈ flatEdges X p ↔ i ∈ X ∧ p.code i = none := by
  change (i ∈ X ∧ ∀ x ∈ p.solutionSet, x i = none) ↔ _
  rw [p.solution_zero_iff]

theorem flatEdges_link (X : Set (Fin n)) (p : GainPartition G n) (e : Link G n) :
    Sum.inr e ∈ flatEdges X p ↔
      (p.code e.tail = none ∧ p.code e.head = none) ∨
      ∃ r a b, p.code e.tail = some (r,a) ∧ p.code e.head = some (r,b) ∧ b = a*e.gain := by
  change (True ∧ ∀ x ∈ p.solutionSet, x e.head = gainAct G (x e.tail) e.gain) ↔ _
  rw [true_and, p.solution_link_iff]

theorem partition_solutions_subset (X : Set (Fin n)) (p : GainPartition G n) :
    p.solutionSet ⊆ solutions G n (flatEdges X p) := fun x hx _e he => he.2 x hx

/-- An implied oriented link equation is present regardless of the chosen canonical orientation. -/
theorem flatEdges_solution_link (X : Set (Fin n)) (p : GainPartition G n)
    (i j : Fin n) (g : G) (hij : i ≠ j)
    (h : ∀ x ∈ p.solutionSet, x j = gainAct G (x i) g)
    {x : Fin n → Option G} (hx : x ∈ solutions G n (flatEdges X p)) :
    x j = gainAct G (x i) g := by
  by_cases hlt : i < j
  · let e : Link G n := ⟨i,j,hlt,g⟩
    have he : Sum.inr e ∈ flatEdges X p := ⟨by trivial,h⟩
    exact hx (Sum.inr e) he
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) hij.symm
    let e : Link G n := ⟨j,i,hji,g⁻¹⟩
    have he : Sum.inr e ∈ flatEdges X p := ⟨by trivial,
      fun y hy => (gainAct_reverse _ _ _).mp (h y hy)⟩
    have heq : x i = gainAct G (x j) g⁻¹ := hx (Sum.inr e) he
    simpa only [inv_inv] using (gainAct_reverse _ _ _).mp heq

end Dowling
