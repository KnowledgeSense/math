import Dowling.BraidBlockIntervals

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

 theorem SingleBalancedBlock.exists_potentials {p : GainPartition G (n+1)}
    (hp : p.SingleBalancedBlock) : ∃ u : Fin (n+1) → G, p=braidTop u := by
  obtain ⟨r,hr⟩ := hp
  choose u hu using hr
  have hr0 : r=0 := le_antisymm (p.least 0 r (u 0) (hu 0)) (Fin.zero_le _)
  subst r
  have hu0 : u 0=1 := by
    have he := (hu 0).symm.trans (p.rooted 0 0 (u 0) (hu 0))
    exact congrArg Prod.snd (Option.some.inj he)
  refine ⟨u,ext_code ?_⟩
  funext i
  change p.code i=some (0,(u 0)⁻¹*u i)
  rw [hu0,inv_one,one_mul]
  exact hu i

 theorem SingleBalancedBlock.lower_orderIso {p : GainPartition G n}
    (hp : p.SingleBalancedBlock) : Nonempty (GainPartition Unit (n-1) ≃o Set.Iic p) := by
  cases n with
  | zero => obtain ⟨r,_⟩ := hp; exact Fin.elim0 r
  | succ n =>
    obtain ⟨u,rfl⟩ := hp.exists_potentials
    exact ⟨braidLowerOrderIso u⟩

/-- Every actual balanced complete block has the ordinary braid Z invariant,
with the essential vertex-to-rank shift retained, including a singleton block. -/
theorem SingleBalancedBlock.partitionZ [Fintype G] {p : GainPartition G n}
    (hp : p.SingleBalancedBlock) : Dowling.partitionZ p=fullZ Unit (n-1) := by
  cases n with
  | zero => obtain ⟨r,_⟩ := hp; exact Fin.elim0 r
  | succ n =>
    obtain ⟨u,rfl⟩ := hp.exists_potentials
    exact braidTop_partitionZ u

end Dowling.GainPartition
