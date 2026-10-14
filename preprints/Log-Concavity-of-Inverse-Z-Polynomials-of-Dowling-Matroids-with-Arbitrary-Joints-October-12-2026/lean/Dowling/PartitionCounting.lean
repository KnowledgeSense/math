import Dowling.PartitionAppendRank

noncomputable section
namespace Dowling
open scoped Classical BigOperators
variable {G : Type*} [Group G] [Fintype G]

/-- Literal rank distribution of the full group-partition flat lattice. -/
def whitneyCount (G : Type*) [Group G] [Fintype G] (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : GainPartition G n => p.roots.card = k)).card

theorem sum_partitions_succ {R : Type*} [CommSemiring R] (n : ℕ) (f : ℕ → R) :
    (∑ p : GainPartition G (n+1), f p.roots.card) =
      ∑ p : GainPartition G n,
        (f (p.roots.card+1) + (1+(Fintype.card G : R)*p.roots.card)*f p.roots.card) := by
  rw [← Equiv.sum_comp (GainPartition.appendEquiv (G := G) (n := n))]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  change (∑ c : p.LastChoice, f (p.append c).roots.card) = _
  rw [Fintype.sum_option]
  simp only [GainPartition.append_new_roots_card,GainPartition.append_existing_roots_card]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : Fintype.card (Option ({j // p.IsRoot j} × G)) = 1+p.roots.card*Fintype.card G := by
    rw [Fintype.card_option,Fintype.card_prod,Fintype.card_subtype]
    change p.roots.card*Fintype.card G+1 = _
    omega
  rw [Finset.card_univ,hc]
  push_cast
  ring

theorem whitneyCount_above (n k : ℕ) (hk : n < k) : whitneyCount G n k = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have he := (Finset.mem_filter.mp hp).2
  have := p.roots_card_le
  omega

theorem whitneyCount_sum {R : Type*} [CommSemiring R] (n : ℕ) (f : ℕ → R) :
    (∑ p : GainPartition G n, f p.roots.card) =
      ∑ k ∈ Finset.range (n+1), (whitneyCount G n k : R)*f k := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun p _ => Finset.mem_range.mpr (Nat.lt_succ_of_le p.roots_card_le))]
  apply Finset.sum_congr rfl
  intro k _
  have h : (∑ p ∈ Finset.univ.filter (fun p : GainPartition G n => p.roots.card = k), f p.roots.card) =
      ∑ _p ∈ Finset.univ.filter (fun p : GainPartition G n => p.roots.card = k), f k := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  rw [h,Finset.sum_const,nsmul_eq_mul]
  rfl

end Dowling
