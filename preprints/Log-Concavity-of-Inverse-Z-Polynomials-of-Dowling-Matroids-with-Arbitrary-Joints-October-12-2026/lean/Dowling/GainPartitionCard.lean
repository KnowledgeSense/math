import Dowling.ConstraintPartitions
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Fintype.Card

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem roots_card_le (p : GainPartition G n) : p.roots.card ≤ n := by
  simpa using Finset.card_le_card (Finset.subset_univ p.roots)

theorem solution_card_roots [Finite G] (p : GainPartition G n) :
    Nat.card p.solutionSet = (Nat.card G + 1) ^ p.roots.card := by
  have hc : Nat.card {j // p.IsRoot j} = p.roots.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [solution_card, hc]

/-- Inclusion of actual solution spaces reverses the number of imposed independent equations. -/
theorem roots_card_mono [Finite G] (p q : GainPartition G n)
    (h : q.solutionSet ⊆ p.solutionSet) : q.roots.card ≤ p.roots.card := by
  let := Fintype.ofFinite G
  have hc := Nat.card_le_card_of_injective (fun x : q.solutionSet => (⟨x.val,h x.property⟩ : p.solutionSet))
    (by intro x y he; exact Subtype.ext (congrArg (fun z : p.solutionSet => z.val) he))
  rw [solution_card_roots, solution_card_roots] at hc
  have hb : 1 < Nat.card G + 1 := by have := Finite.card_pos (α := G); omega
  exact (pow_le_pow_iff_right₀ hb).mp hc

theorem roots_card_eq [Finite G] (p q : GainPartition G n)
    (h : p.solutionSet = q.solutionSet) : p.roots.card = q.roots.card := by
  exact le_antisymm (q.roots_card_mono p h.subset) (p.roots_card_mono q h.symm.subset)

end Dowling.GainPartition
