import Dowling.GainPartitionErase

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

/-- Impose a gain relation between two different free roots, keeping the smaller root. -/
def mergeBlocks (p : GainPartition G n) (r s : Fin n) (h : G)
    (hr : p.IsRoot r) (hrs : r < s) : GainPartition G n where
  code i := match p.code i with
    | none => none
    | some (u,g) => if u = s then some (r,h*g) else some (u,g)
  rooted := by
    intro i j g hi
    have hpr : p.code r = some (r,1) := hr
    cases hpi : p.code i with
    | none => simp [hpi] at hi
    | some v =>
      rcases v with ⟨u,a⟩
      by_cases hu : u = s
      · subst u
        simp only [hpi, ite_true, Option.some.injEq, Prod.mk.injEq] at hi
        rcases hi with ⟨rfl,rfl⟩
        simp [hpr, hrs.ne]
      · simp only [hpi, hu, ite_false, Option.some.injEq, Prod.mk.injEq] at hi
        rcases hi with ⟨rfl,rfl⟩
        simp [p.rooted i u a hpi, hu]
  least := by
    intro i j g hi
    cases hpi : p.code i with
    | none => simp [hpi] at hi
    | some v =>
      rcases v with ⟨u,a⟩
      by_cases hu : u = s
      · subst u
        simp only [hpi, ite_true, Option.some.injEq, Prod.mk.injEq] at hi
        rcases hi with ⟨rfl,rfl⟩
        exact hrs.le.trans (p.least i s a hpi)
      · simp only [hpi, hu, ite_false, Option.some.injEq, Prod.mk.injEq] at hi
        rcases hi with ⟨rfl,rfl⟩
        exact p.least i u a hpi

theorem mergeBlocks_assignment (p : GainPartition G n) (r s : Fin n) (h : G)
    (hr : p.IsRoot r) (hrs : r < s) (a : Fin n → Option G) :
    (p.mergeBlocks r s h hr hrs).assignment a =
      p.assignment (Function.update a s (gainAct G (a r) h)) := by
  funext i
  cases hi : p.code i with
  | none => simp [assignment, mergeBlocks, hi]
  | some v =>
    rcases v with ⟨u,g⟩
    by_cases hu : u = s
    · subst u
      simp [assignment, mergeBlocks, hi, gainAct_mul]
    · simp [assignment, mergeBlocks, hi, hu]

theorem mergeBlocks_solutionSet (p : GainPartition G n) (r s : Fin n) (h : G)
    (hr : p.IsRoot r) (hs : p.IsRoot s) (hrs : r < s) :
    (p.mergeBlocks r s h hr hrs).solutionSet =
      {x ∈ p.solutionSet | x s = gainAct G (x r) h} := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    rw [mergeBlocks_assignment]
    refine ⟨p.assignment_mem _, ?_⟩
    rw [p.assignment_root _ s hs, p.assignment_root _ r hr]
    simp [Function.update_of_ne hrs.ne]
  · rintro ⟨⟨a,rfl⟩,ha⟩
    rw [p.assignment_root a s hs, p.assignment_root a r hr] at ha
    refine ⟨a, ?_⟩
    rw [mergeBlocks_assignment]
    congr 1
    funext j
    by_cases hj : j = s
    · subst j
      simp [ha]
    · simp [Function.update_of_ne hj]

end Dowling.GainPartition
