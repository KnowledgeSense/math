import Dowling.LowerProductInvariant
import Dowling.PartitionKL

noncomputable section
namespace Dowling
open MatroidInverseZ
open scoped Classical BigOperators
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

/-- The actual restriction KL invariant factors over precisely the literal
zero block and balanced blocks of the flat. -/
theorem partitionP_product (p : GainPartition G n) :
    partitionP p = ∏ c : Option (Fin n), partitionP (p.fiberTop c) := by
  have h := intervalP_transport (lowerProductEmbedding p) (lowerProductEmbedding_interval p)
    (fun q => ∑ c, partitionRank (q c).val) partitionRank
    (fun a b => by rw [lowerProductEmbedding_rank,lowerProductEmbedding_rank])
    (lowerProductBottom p) (lowerProductTop p)
  rw [lowerProductEmbedding_bottom,lowerProductEmbedding_top] at h
  change partitionP p = _ at h
  rw [h]
  trans ∏ c : Option (Fin n), intervalP (fun q : Set.Iic (p.fiberTop c) => partitionRank q.val)
    (lowerProductBottom p c) (lowerProductTop p c)
  · have hm (c : Option (Fin n)) : Monotone (fun q : Set.Iic (p.fiberTop c) =>
        partitionRank (G := G) q.val) := by
      intro a b hab
      exact partitionRank_monotone (G := G) (n := (p.fiber c).card) hab
    have hab : lowerProductBottom p ≤ lowerProductTop p := by
      intro c
      change (⊥ : GainPartition G (p.fiber c).card) ≤ p.fiberTop c
      exact bot_le
    have hz := intervalP_pi (fun c : Option (Fin n) => Set.Iic (p.fiberTop c))
      (fun c (q : Set.Iic (p.fiberTop c)) => partitionRank (G := G) q.val) hm
      (lowerProductBottom p) (lowerProductTop p) hab
    exact hz
  apply Finset.prod_congr rfl
  intro c _
  rw [partitionIic_intervalP]
  rfl

end Dowling
