import Dowling.BalancedBlocks

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

/-- Connected components of the literal selected gain-link graph, including isolated vertices. -/
abbrev Component (S : Set (Edge G n)) := Quotient (componentSetoid S)

/-- A connected component whose ordered gains are balanced and which contains no joint. -/
def BalancedComponent (S : Set (Edge G n)) :=
  {c : Component S // ∃ i, Quotient.mk (componentSetoid S) i = c ∧ BalancedAt S i}

def balancedCount (S : Set (Edge G n)) : ℕ := Nat.card (BalancedComponent S)

namespace GainPartition

def rootComponent (p : GainPartition G n) (S : Set (Edge G n))
    (hp : p.solutionSet = solutions G n S) (r : {r // p.IsRoot r}) : BalancedComponent S :=
  ⟨Quotient.mk (componentSetoid S) r.val, r.val, rfl, p.root_balanced S hp r.val r.property⟩

theorem rootComponent_bijective (p : GainPartition G n) (S : Set (Edge G n))
    (hp : p.solutionSet = solutions G n S) : Function.Bijective (p.rootComponent S hp) := by
  constructor
  · intro r s h
    have hc : Quotient.mk (componentSetoid S) r.val = Quotient.mk (componentSetoid S) s.val :=
      congrArg (fun c : BalancedComponent S => c.val) h
    apply Subtype.ext
    exact p.connected_roots_eq S hp r.val s.val r.property s.property (Quotient.exact hc)
  · intro c
    obtain ⟨i,hi,hbi⟩ := c.property
    have hn := (p.code_nonzero_iff_balanced S hp i).mpr hbi
    cases hc : p.code i with
    | none => exact False.elim (hn hc)
    | some v =>
      rcases v with ⟨r,a⟩
      refine ⟨⟨r,p.rooted i r a hc⟩, ?_⟩
      apply Subtype.ext
      exact (Quotient.sound (p.connected_to_root S hp i r a hc)).trans hi

/-- Each free block is exactly one actual balanced connected component. -/
def balancedComponentEquiv (p : GainPartition G n) (S : Set (Edge G n))
    (hp : p.solutionSet = solutions G n S) : {r // p.IsRoot r} ≃ BalancedComponent S :=
  Equiv.ofBijective (p.rootComponent S hp) (p.rootComponent_bijective S hp)

theorem balancedCount_eq_roots (p : GainPartition G n) (S : Set (Edge G n))
    (hp : p.solutionSet = solutions G n S) : balancedCount S = p.roots.card := by
  rw [balancedCount, Nat.card_congr (p.balancedComponentEquiv S hp).symm,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

end GainPartition

variable [Finite G]

/-- The standard frame rank n-b, derived for every edge subset. -/
theorem constraintRank_eq_balancedCount (S : Set (Edge G n)) :
    constraintRank S = n - balancedCount S := by
  rw [(partitionOf S).balancedCount_eq_roots S (partitionOf_solutionSet S)]
  rfl

theorem fullMatroid_eRk_balanced (S : Set (Edge G n)) :
    (fullMatroid G n).eRk S = ((n - balancedCount S : ℕ) : ℕ∞) := by
  rw [fullMatroid_eRk, constraintRank_eq_balancedCount]

theorem matroid_eRk_balanced (X : Set (Fin n)) (S : Set (Edge G n))
    (hS : S ⊆ ground G n X) :
    (matroid G n X).eRk S = ((n - balancedCount S : ℕ) : ℕ∞) := by
  rw [matroid_eRk X S hS, constraintRank_eq_balancedCount]

end Dowling
