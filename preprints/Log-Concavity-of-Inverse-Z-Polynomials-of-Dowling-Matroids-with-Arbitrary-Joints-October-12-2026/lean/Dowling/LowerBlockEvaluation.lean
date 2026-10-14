import Dowling.LowerProductInvariant
import Dowling.BraidBlockSingle

noncomputable section
namespace Dowling
open MatroidInverseZ
open scoped Classical BigOperators
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

theorem partitionZ_of_size_zero (p : GainPartition G n) (hn : n=0) : partitionZ p=1 := by
  subst n
  have hp : p=⊥ := by
    apply GainPartition.code_injective
    funext i
    exact Fin.elim0 i
  rw [hp,partitionZ,zKernel_diag]

theorem partitionZ_zero_fiber (p : GainPartition G n) :
    partitionZ (p.fiberTop none)=fullZ G (p.fiber none).card := by
  rw [p.fiberTop_zero]
  exact partitionZ_top _

theorem partitionZ_balanced_fiber (p : GainPartition G n) (r : Fin n) :
    partitionZ (p.fiberTop (some r))=fullZ Unit ((p.fiber (some r)).card-1) := by
  by_cases hc : (p.fiber (some r)).card=0
  · rw [partitionZ_of_size_zero _ hc,hc,Nat.zero_sub,fullZ_zero]
  · exact GainPartition.SingleBalancedBlock.partitionZ (p.fiberTop_some_single r (Nat.pos_of_ne_zero hc))

/-- Full lower-flat evaluation, including empty zero blocks, empty colors and
singleton balanced blocks without a missing rank shift. -/
theorem partitionZ_block_formula (p : GainPartition G n) :
    partitionZ p=fullZ G (p.fiber none).card *
      ∏ r : Fin n, fullZ Unit ((p.fiber (some r)).card-1) := by
  rw [partitionZ_product,Fintype.prod_option,partitionZ_zero_fiber]
  simp only [partitionZ_balanced_fiber]

theorem configuration_lower_z (p : Configuration G (Set.univ : Set (Fin n))) :
    zKernel (configurationRank Set.univ) (⊥ : Configuration G Set.univ) p=partitionZ p.val := by
  let e := fullPartitionOrderIso (G := G) n
  have h := zKernel_interval_transport e.toOrderEmbedding
    (fun _ _ y _ _ => ⟨e.symm y,e.apply_symm_apply y⟩)
    partitionRank (configurationRank Set.univ) (fun _ _ => rfl) ⊥ p.val
  change zKernel (configurationRank Set.univ) (e ⊥) (e p.val) = _ at h
  rw [e.map_bot] at h
  exact h

end Dowling
