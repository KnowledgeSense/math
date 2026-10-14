import Dowling.PartitionBounds
import Dowling.Invariants
import Dowling.PartitionUpperEquiv

noncomputable section
namespace Dowling
open scoped Classical BigOperators
open MatroidInverseZ
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

def partitionRank (p : GainPartition G n) : ℕ := n-p.roots.card

theorem partitionRank_monotone : Monotone (partitionRank (G := G) (n := n)) := by
  intro p q hpq
  exact Nat.sub_le_sub_left (p.roots_card_mono q hpq) n

def partitionZ (p : GainPartition G n) : Polynomial ℤ := zKernel partitionRank ⊥ p

def fullPartitionOrderIso (n : ℕ) : GainPartition G n ≃o Configuration G (Set.univ : Set (Fin n)) where
  toFun p := ⟨p,admissible_univ p⟩
  invFun p := p.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem partitionZ_top (n : ℕ) : partitionZ (⊤ : GainPartition G n) = fullZ G n := by
  let e := fullPartitionOrderIso (G := G) n
  have h := zKernel_interval_transport e.toOrderEmbedding
    (fun _ _ y _ _ => ⟨e.symm y,e.apply_symm_apply y⟩)
    partitionRank (configurationRank Set.univ) (fun _ _ => rfl) ⊥ ⊤
  change zKernel (configurationRank Set.univ) (e ⊥) (e ⊤) = _ at h
  rw [e.map_bot,e.map_top] at h
  exact h.symm

instance partitionIicLocallyFiniteOrder (p : GainPartition G n) : LocallyFiniteOrder (Set.Iic p) :=
  Fintype.toLocallyFiniteOrder

def partitionIicEmbedding (p : GainPartition G n) : Set.Iic p ↪o GainPartition G n where
  toFun q := q.val
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

omit [Fintype G] in
theorem partitionIic_interval (p : GainPartition G n) :
    ∀ a b y, partitionIicEmbedding p a ≤ y → y ≤ partitionIicEmbedding p b →
      ∃ x, partitionIicEmbedding p x=y := by
  intro _ b y _ hyb
  exact ⟨⟨y,hyb.trans b.property⟩,rfl⟩

theorem partitionIic_zKernel (p : GainPartition G n) (a b : Set.Iic p) :
    zKernel (fun q : Set.Iic p => partitionRank q.val) a b = zKernel partitionRank a.val b.val := by
  exact (zKernel_interval_transport (partitionIicEmbedding p) (partitionIic_interval p)
    (fun q : Set.Iic p => partitionRank q.val) partitionRank (fun _ _ => rfl) a b).symm

end Dowling
