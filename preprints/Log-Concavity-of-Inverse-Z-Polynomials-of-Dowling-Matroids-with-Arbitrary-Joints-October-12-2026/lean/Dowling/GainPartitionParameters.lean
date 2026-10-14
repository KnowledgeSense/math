import Dowling.GainPartition
import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

def extend (p : GainPartition G n) (a : {j // p.IsRoot j} → Option G) (j : Fin n) : Option G :=
  if hj : p.IsRoot j then a ⟨j,hj⟩ else none

@[simp] theorem extend_root (p : GainPartition G n) (a : {j // p.IsRoot j} → Option G)
    (j : {j // p.IsRoot j}) : p.extend a j = a j := by
  simp [extend, j.property]

/-- The free balanced blocks are independent parameters, with no quotient multiplicity. -/
def solutionEquiv (p : GainPartition G n) : p.solutionSet ≃ ({j // p.IsRoot j} → Option G) where
  toFun x j := x.val j
  invFun a := ⟨p.assignment (p.extend a), ⟨_,rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have hx := (p.mem_solutionSet x.val).mp x.property
    cases hi : p.code i with
    | none => simpa only [assignment, hi] using (hx.1 i hi).symm
    | some v =>
      rcases v with ⟨j,g⟩
      have hj : p.IsRoot j := p.rooted i j g hi
      simp only [assignment, hi, extend, dite_eq_left hj]
      exact (hx.2 i j g hi).symm
  right_inv a := by
    funext j
    change p.assignment (p.extend a) j = a j
    rw [p.assignment_root _ j j.property]
    exact p.extend_root a j

/-- Exact finite solution count, retaining the zero choice in every free block. -/
theorem solution_card [Finite G] (p : GainPartition G n) :
    Nat.card p.solutionSet = (Nat.card G + 1) ^ Nat.card {j // p.IsRoot j} := by
  rw [Nat.card_congr p.solutionEquiv, Nat.card_fun, Finite.card_option]

end Dowling.GainPartition
