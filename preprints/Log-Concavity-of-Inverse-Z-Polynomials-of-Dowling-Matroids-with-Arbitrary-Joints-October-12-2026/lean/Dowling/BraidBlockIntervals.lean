import Dowling.BraidBlockRank
import Dowling.PartitionInvariants

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

 def braidLowerEmbedding (u : Fin (n+1) → G) : GainPartition Unit n ↪o GainPartition G (n+1) where
  toFun p := p.braidLift u
  inj' := by
    intro p q h
    apply le_antisymm
    · exact (braidLift_le_iff p q u).mp h.le
    · exact (braidLift_le_iff q p u).mp h.ge
  map_rel_iff' := braidLift_le_iff _ _ u

 def braidLowerIicEmbedding (u : Fin (n+1) → G) : GainPartition Unit n ↪o Set.Iic (braidTop u) where
  toFun p := ⟨p.braidLift u,p.braidLift_le_braidTop u⟩
  inj' := by intro p q h; exact (braidLowerEmbedding u).injective (congrArg Subtype.val h)
  map_rel_iff' := braidLift_le_iff _ _ u

 def braidLowerOrderIso (u : Fin (n+1) → G) : GainPartition Unit n ≃o Set.Iic (braidTop u) :=
  OrderIso.ofSurjective (braidLowerIicEmbedding u) (by
    intro p
    obtain ⟨q,hq⟩ := braidLift_surjective_below u p.val p.property
    exact ⟨q,Subtype.ext hq⟩)

 theorem braidLowerEmbedding_interval (u : Fin (n+1) → G) :
    ∀ a b y, braidLowerEmbedding u a ≤ y → y ≤ braidLowerEmbedding u b →
      ∃ x, braidLowerEmbedding u x=y := by
  intro _ b y _ hy
  exact braidLift_surjective_below u y (hy.trans (b.braidLift_le_braidTop u))

 theorem braidLowerEmbedding_bot (u : Fin (n+1) → G) : braidLowerEmbedding u ⊥=⊥ := by
  apply ext_code
  funext i
  change some ((discrete : GainPartition Unit n).unitBlockRoot i,
    (u ((discrete : GainPartition Unit n).unitBlockRoot i))⁻¹*u i)=some (i,1)
  have hr : (discrete : GainPartition Unit n).unitBlockRoot i=i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [unitBlockRoot,discrete]
  simp [hr]

 theorem braidLowerEmbedding_top (u : Fin (n+1) → G) : braidLowerEmbedding u ⊤=braidTop u := by
  apply ext_code
  funext i
  change some ((zeroPartition : GainPartition Unit n).unitBlockRoot i,
    (u ((zeroPartition : GainPartition Unit n).unitBlockRoot i))⁻¹*u i)=some (0,(u 0)⁻¹*u i)
  have hr : (zeroPartition : GainPartition Unit n).unitBlockRoot i=0 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [unitBlockRoot,zeroPartition]
  rw [hr]

 theorem braidLowerEmbedding_rank (u : Fin (n+1) → G) (p : GainPartition Unit n) :
    partitionRank (braidLowerEmbedding u p)=partitionRank p := p.braidLift_rank u

 theorem braidTop_partitionZ [Fintype G] (u : Fin (n+1) → G) :
    partitionZ (braidTop u)=fullZ Unit n := by
  have h := MatroidInverseZ.zKernel_interval_transport (braidLowerEmbedding u)
    (braidLowerEmbedding_interval u) partitionRank partitionRank
    (fun a b => by rw [braidLowerEmbedding_rank,braidLowerEmbedding_rank]) ⊥ ⊤
  rw [braidLowerEmbedding_bot,braidLowerEmbedding_top] at h
  exact h.trans (partitionZ_top n)

end Dowling.GainPartition
