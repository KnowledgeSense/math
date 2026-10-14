import Dowling.PartitionFiberTypes
import Dowling.PartitionInvariants
import Dowling.ZDependentProduct

noncomputable section
namespace Dowling
open MatroidInverseZ
open scoped Classical BigOperators
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

def lowerProductEmbedding (p : GainPartition G n) :
    (∀ c : Option (Fin n), Set.Iic (p.fiberTop c)) ↪o GainPartition G n :=
  p.lowerProductOrderIso.toOrderEmbedding.comp (partitionIicEmbedding p)

omit [Fintype G] in
theorem lowerProductEmbedding_interval (p : GainPartition G n) :
    ∀ a b y, lowerProductEmbedding p a ≤ y → y ≤ lowerProductEmbedding p b →
      ∃ x, lowerProductEmbedding p x=y := by
  intro _ b y _ hyb
  have hy : y ≤ p := hyb.trans (p.lowerProductOrderIso b).property
  obtain ⟨x,hx⟩ := p.lowerProductOrderIso.surjective ⟨y,hy⟩
  exact ⟨x,congrArg Subtype.val hx⟩

omit [Fintype G] in
theorem lowerProductEmbedding_rank (p : GainPartition G n)
    (q : ∀ c : Option (Fin n), Set.Iic (p.fiberTop c)) :
    partitionRank (lowerProductEmbedding p q) = ∑ c, partitionRank (q c).val :=
  p.glue_rank (fun c => (q c).val)

def lowerProductBottom (p : GainPartition G n) : ∀ c : Option (Fin n), Set.Iic (p.fiberTop c) :=
  fun c => ⟨⊥,by change (⊥ : GainPartition G (p.fiber c).card) ≤ p.fiberTop c; exact bot_le⟩

def lowerProductTop (p : GainPartition G n) : ∀ c : Option (Fin n), Set.Iic (p.fiberTop c) :=
  fun c => ⟨p.fiberTop c,by change p.fiberTop c ≤ p.fiberTop c; exact le_rfl⟩

omit [Fintype G] in
theorem lowerProductEmbedding_bottom (p : GainPartition G n) :
    lowerProductEmbedding p (lowerProductBottom p)=⊥ := by
  apply GainPartition.solutionSet_injective
  ext x
  change x ∈ (p.glue (fun c => (⊥ : GainPartition G (p.fiber c).card))).solutionSet ↔
    x ∈ GainPartition.discrete.solutionSet
  rw [p.mem_glue_solutionSet,GainPartition.discrete_solutionSet]
  simp only [show ∀ c, (⊥ : GainPartition G (p.fiber c).card).solutionSet=Set.univ from
    fun _ => GainPartition.discrete_solutionSet,Set.mem_univ,implies_true]

omit [Fintype G] in
theorem lowerProductEmbedding_top (p : GainPartition G n) :
    lowerProductEmbedding p (lowerProductTop p)=p := p.glue_fiberTop

/-- The actual restriction Z invariant factors over precisely the literal
zero block and balanced blocks of the flat. -/
theorem partitionZ_product (p : GainPartition G n) :
    partitionZ p = ∏ c : Option (Fin n), partitionZ (p.fiberTop c) := by
  have h := zKernel_interval_transport (lowerProductEmbedding p) (lowerProductEmbedding_interval p)
    (fun q => ∑ c, partitionRank (q c).val) partitionRank
    (fun a b => by rw [lowerProductEmbedding_rank,lowerProductEmbedding_rank])
    (lowerProductBottom p) (lowerProductTop p)
  rw [lowerProductEmbedding_bottom,lowerProductEmbedding_top] at h
  change partitionZ p = _ at h
  rw [h]
  trans ∏ c : Option (Fin n), zKernel (fun q : Set.Iic (p.fiberTop c) => partitionRank q.val)
    (lowerProductBottom p c) (lowerProductTop p c)
  · have hm (c : Option (Fin n)) : Monotone (fun q : Set.Iic (p.fiberTop c) =>
        partitionRank (G := G) q.val) := by
      intro a b hab
      exact partitionRank_monotone (G := G) (n := (p.fiber c).card) hab
    have hab : lowerProductBottom p ≤ lowerProductTop p := by
      intro c
      change (⊥ : GainPartition G (p.fiber c).card) ≤ p.fiberTop c
      exact bot_le
    have hz := zKernel_pi (fun c : Option (Fin n) => Set.Iic (p.fiberTop c))
      (fun c (q : Set.Iic (p.fiberTop c)) => partitionRank (G := G) q.val) hm
      (lowerProductBottom p) (lowerProductTop p) hab
    exact hz
  apply Finset.prod_congr rfl
  intro c _
  rw [partitionIic_zKernel]
  rfl

end Dowling
