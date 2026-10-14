import Dowling.KLDependentProduct
import Dowling.PartitionInvariants

noncomputable section
namespace Dowling
open MatroidInverseZ
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

def partitionP (p : GainPartition G n) : Polynomial ℤ := intervalP partitionRank ⊥ p

theorem partitionP_top (n : ℕ) : partitionP (⊤ : GainPartition G n)=fullP G n := by
  let e := fullPartitionOrderIso (G := G) n
  have h := kl_interval_transport e.toOrderEmbedding
    (fun _ _ y _ _ => ⟨e.symm y,e.apply_symm_apply y⟩)
    partitionRank (configurationRank Set.univ) (fun _ _ => rfl) ⊥ ⊤
  change kl (configurationRank Set.univ) (e ⊤) (e ⊥)=_ at h
  rw [e.map_bot,e.map_top] at h
  exact h.symm

theorem partitionIic_intervalP (p : GainPartition G n) (a b : Set.Iic p) :
    intervalP (fun q : Set.Iic p => partitionRank q.val) a b=intervalP partitionRank a.val b.val :=
  (intervalP_transport (partitionIicEmbedding p) (partitionIic_interval p)
    (fun q : Set.Iic p => partitionRank q.val) partitionRank (fun _ _ => rfl) a b).symm

end Dowling
