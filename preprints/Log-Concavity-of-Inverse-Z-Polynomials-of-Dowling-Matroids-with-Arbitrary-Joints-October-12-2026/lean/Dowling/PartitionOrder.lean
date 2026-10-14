import Dowling.MatroidFlats

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

instance : PartialOrder (GainPartition G n) where
  le p q := q.solutionSet ⊆ p.solutionSet
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ hpq hqr := hqr.trans hpq
  le_antisymm _ _ hpq hqp := GainPartition.solutionSet_injective (Set.Subset.antisymm hqp hpq)

theorem partition_le_iff (p q : GainPartition G n) : p ≤ q ↔ q.solutionSet ⊆ p.solutionSet := Iff.rfl

instance [Finite G] : Finite (GainPartition G n) := by
  let := Fintype.ofFinite G
  apply Finite.of_injective (fun p : GainPartition G n => p.code)
  intro p q h
  cases p
  cases q
  cases h
  rfl

instance [Finite G] : Fintype (GainPartition G n) := Fintype.ofFinite _

theorem flatEdges_mono (X : Set (Fin n)) {p q : GainPartition G n} (h : p ≤ q) :
    flatEdges X p ⊆ flatEdges X q := fun _e he => ⟨he.1,fun x hx => he.2 x (h hx)⟩

theorem flatEdges_le_iff (X : Set (Fin n)) (p q : GainPartition G n)
    (hp : Admissible X p) (hq : Admissible X q) : flatEdges X p ⊆ flatEdges X q ↔ p ≤ q := by
  constructor
  · intro h
    have hs := solutions_antitone h
    rw [flatEdges_solutions X p hp, flatEdges_solutions X q hq] at hs
    exact hs
  · exact flatEdges_mono X

/-- Admissible partial group partitions, with their actual refinement order. -/
def Configuration (G : Type*) [Group G] {n : ℕ} (X : Set (Fin n)) :=
  {p : GainPartition G n // Admissible X p}

instance (X : Set (Fin n)) : PartialOrder (Configuration G X) := inferInstanceAs (PartialOrder {p // Admissible X p})
instance [Finite G] (X : Set (Fin n)) : Fintype (Configuration G X) := inferInstanceAs (Fintype {p // Admissible X p})

end Dowling
