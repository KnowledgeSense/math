import Dowling.FlatEdges

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem flatEdges_zero_link (X : Set (Fin n)) (p : GainPartition G n)
    (i j : Fin n) (g : G) (hij : i ≠ j) (hi : p.code i = none) (hj : p.code j = none)
    {x : Fin n → Option G} (hx : x ∈ solutions G n (flatEdges X p)) :
    x j = gainAct G (x i) g := by
  apply flatEdges_solution_link X p i j g hij _ hx
  intro y hy
  have hz := ((p.mem_solutionSet y).mp hy).1
  rw [hz i hi, hz j hj, gainAct_none]

theorem flatEdges_forces_zero (X : Set (Fin n)) (p : GainPartition G n)
    (hp : Admissible X p) {x : Fin n → Option G} (hx : x ∈ solutions G n (flatEdges X p))
    (i : Fin n) (hi : p.code i = none) : x i = none := by
  rcases hp i hi with ⟨j,hjX,hj⟩ | ⟨hG,j,hji,hj⟩
  · have hz : x j = none := hx (Sum.inl j) ((flatEdges_joint X p j).mpr ⟨hjX,hj⟩)
    by_cases hij : i = j
    · simpa only [hij] using hz
    · have h := flatEdges_zero_link X p i j 1 hij hi hj hx
      rw [gainAct_one] at h
      exact h.symm.trans hz
  · let := hG
    obtain ⟨g,hg⟩ := exists_ne (1:G)
    have h1 := flatEdges_zero_link X p i j 1 hji.symm hi hj hx
    have h2 := flatEdges_zero_link X p i j g hji.symm hi hj hx
    rw [gainAct_one] at h1
    exact (gainAct_fixed_iff _ _ hg).mp (h2.symm.trans h1)

theorem flatEdges_forces_potential (X : Set (Fin n)) (p : GainPartition G n)
    {x : Fin n → Option G} (hx : x ∈ solutions G n (flatEdges X p))
    (i r : Fin n) (a : G) (hi : p.code i = some (r,a)) :
    x i = gainAct G (x r) a := by
  by_cases hri : r = i
  · subst r
    have hr := p.rooted i i a hi
    have ha : a = 1 := congrArg Prod.snd (Option.some.inj (hi.symm.trans hr))
    simp [ha]
  · apply flatEdges_solution_link X p r i a hri _ hx
    intro y hy
    exact ((p.mem_solutionSet y).mp hy).2 i r a hi

/-- Every admissible zero/potential partition is realized by exactly its available flat edges. -/
theorem flatEdges_solutions (X : Set (Fin n)) (p : GainPartition G n) (hp : Admissible X p) :
    solutions G n (flatEdges X p) = p.solutionSet := by
  apply Set.Subset.antisymm _ (partition_solutions_subset X p)
  intro x hx
  apply (p.mem_solutionSet x).mpr
  exact ⟨flatEdges_forces_zero X p hp hx, flatEdges_forces_potential X p hx⟩

end Dowling
