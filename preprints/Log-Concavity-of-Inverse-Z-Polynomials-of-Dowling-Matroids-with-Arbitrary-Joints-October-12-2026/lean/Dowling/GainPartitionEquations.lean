import Dowling.GainPartitionParameters

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem assignment_mem (p : GainPartition G n) (a : Fin n → Option G) :
    p.assignment a ∈ p.solutionSet := ⟨a,rfl⟩

theorem solution_zero_iff (p : GainPartition G n) (i : Fin n) :
    (∀ x ∈ p.solutionSet, x i = none) ↔ p.code i = none := by
  constructor
  · intro h
    have h1 := h (p.assignment (fun _ => some 1)) (p.assignment_mem _)
    cases hi : p.code i with
    | none => rfl
    | some v =>
      rcases v with ⟨j,g⟩
      simp [assignment, hi, gainAct] at h1
  · intro hi x hx
    exact ((p.mem_solutionSet x).mp hx).1 i hi

/-- Exact universal link equation of a canonical potential partition. -/
theorem solution_link_iff (p : GainPartition G n) (i j : Fin n) (g : G) :
    (∀ x ∈ p.solutionSet, x j = gainAct G (x i) g) ↔
      (p.code i = none ∧ p.code j = none) ∨
      ∃ r a b, p.code i = some (r,a) ∧ p.code j = some (r,b) ∧ b = a*g := by
  constructor
  · intro h
    have h1 := h (p.assignment (fun _ => some 1)) (p.assignment_mem _)
    cases hi : p.code i with
    | none =>
      cases hj : p.code j with
      | none => exact Or.inl ⟨rfl,rfl⟩
      | some v =>
        rcases v with ⟨r,b⟩
        simp [assignment, hi, hj, gainAct] at h1
    | some v =>
      rcases v with ⟨r,a⟩
      cases hj : p.code j with
      | none => simp [assignment, hi, hj, gainAct] at h1
      | some w =>
        rcases w with ⟨s,b⟩
        have hrs : r = s := by
          by_contra hne
          have h2 := h (p.assignment (fun k => if k = r then some 1 else none))
            (p.assignment_mem _)
          simp [assignment, hi, hj, gainAct, Ne.symm hne] at h2
        subst s
        refine Or.inr ⟨r,a,b,rfl,rfl,?_⟩
        simpa [assignment, hi, hj, gainAct] using h1
  · rintro (⟨hi,hj⟩ | ⟨r,a,b,hi,hj,hb⟩) x hx
    · rw [((p.mem_solutionSet x).mp hx).1 i hi,
        ((p.mem_solutionSet x).mp hx).1 j hj, gainAct_none]
    · have he := ((p.mem_solutionSet x).mp hx).2
      rw [he i r a hi, he j r b hj, gainAct_mul, hb]

end Dowling.GainPartition
