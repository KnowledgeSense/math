import Dowling.PartitionOrder
import ThagomizerTuran.MatroidDefinitions

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

/-- Actual flats and admissible potential partitions are order-isomorphic. -/
def configurationOrderIso (X : Set (Fin n)) :
    Configuration G X ≃o MatroidInverseZ.Flat (matroid G n X) where
  toFun p := ⟨flatEdges X p.val, flatEdges_isFlat X p.val p.property⟩
  invFun F := ⟨partitionOf F.val,
    admissible_of_solutions X F.val F.property.subset_ground _ (partitionOf_solutionSet F.val)⟩
  left_inv p := by
    apply Subtype.ext
    apply GainPartition.solutionSet_injective
    exact (partitionOf_solutionSet _).trans (flatEdges_solutions X p.val p.property)
  right_inv F := by
    apply Subtype.ext
    exact (flat_eq_flatEdges X F.val F.property).symm
  map_rel_iff' := by
    intro p q
    exact flatEdges_le_iff X p.val q.val p.property q.property

/-- Rank is the number of vertices minus the actual balanced potential blocks. -/
def configurationRank (X : Set (Fin n)) (p : Configuration G X) : ℕ := n-p.val.roots.card

theorem configurationOrderIso_rank (X : Set (Fin n)) (p : Configuration G X) :
    MatroidInverseZ.flatRank (matroid G n X) (configurationOrderIso X p) = configurationRank X p := by
  change ((matroid G n X).eRk (flatEdges X p.val)).toNat = n-p.val.roots.card
  rw [flatEdges_eRk X p.val p.property]
  rfl

theorem configurationRank_strictMono (X : Set (Fin n)) : StrictMono (configurationRank (G := G) X) := by
  intro p q hpq
  have hs : q.val.solutionSet ⊆ p.val.solutionSet := hpq.le
  have hc := p.val.roots_card_mono q.val hs
  have hn : q.val.roots.card ≠ p.val.roots.card := by
    intro he
    have heq : q.val.solutionSet = p.val.solutionSet := by
      apply Set.eq_of_subset_of_ncard_le hs
      change Nat.card p.val.solutionSet ≤ Nat.card q.val.solutionSet
      rw [GainPartition.solution_card_roots, GainPartition.solution_card_roots, he]
    have hpqe : p = q := Subtype.ext (GainPartition.solutionSet_injective heq.symm)
    exact hpq.ne hpqe
  have hpn := p.val.roots_card_le
  have hqn := q.val.roots_card_le
  change n-p.val.roots.card < n-q.val.roots.card
  omega

end Dowling
