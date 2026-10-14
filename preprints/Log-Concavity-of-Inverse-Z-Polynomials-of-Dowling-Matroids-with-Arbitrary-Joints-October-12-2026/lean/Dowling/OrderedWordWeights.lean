import Dowling.OrderedPartitionEquiv
import Dowling.LowerBlockEvaluation

noncomputable section
namespace Dowling.OccupiedWord
open scoped Classical BigOperators
variable {G : Type*} [Group G] {n k : ℕ}

theorem partition_blockColor (w : OccupiedWord n k) (l : w.Labels G) (i : Fin n) :
    (w.partition l).blockColor i=(w.val i).map w.root := by
  cases hi : w.val i <;> simp [GainPartition.blockColor,partition_code,hi]

theorem partition_zero_fiber (w : OccupiedWord n k) (l : w.Labels G) :
    (w.partition l).fiber none=w.fiber none := by
  ext i
  simp only [GainPartition.fiber,fiber,Finset.mem_filter,Finset.mem_univ,true_and,
    w.partition_blockColor l i,Option.map_eq_none_iff]

theorem partition_root_fiber (w : OccupiedWord n k) (l : w.Labels G) (c : Fin k) :
    (w.partition l).fiber (some (w.root c))=w.fiber (some c) := by
  ext i
  simp only [GainPartition.fiber,fiber,Finset.mem_filter,Finset.mem_univ,true_and,
    w.partition_blockColor l i]
  cases hi : w.val i with
  | none => simp
  | some d => simp only [Option.map_some,Option.some.injEq,w.root_injective.eq_iff]

theorem partition_unused_fiber (w : OccupiedWord n k) (l : w.Labels G) (r : Fin n)
    (hr : r ∉ Finset.univ.image w.root) : (w.partition l).fiber (some r)=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have he := (Finset.mem_filter.mp hi).2
  rw [w.partition_blockColor l i] at he
  cases hw : w.val i with
  | none => simp [hw] at he
  | some c =>
    simp only [hw,Option.map_some,Option.some.injEq] at he
    exact hr (Finset.mem_image.mpr ⟨c,Finset.mem_univ _,he⟩)

variable [Fintype G]

theorem partitionZ_weight (w : OccupiedWord n k) (l : w.Labels G) :
    partitionZ (w.partition l)=fullZ G (w.fiber none).card *
      ∏ c : Fin k, fullZ Unit ((w.fiber (some c)).card-1) := by
  rw [partitionZ_block_formula,w.partition_zero_fiber]
  congr 1
  calc
    (∏ r : Fin n, fullZ Unit (((w.partition l).fiber (some r)).card-1)) =
        ∏ r ∈ Finset.univ.image w.root,
          fullZ Unit (((w.partition l).fiber (some r)).card-1) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro r _ hr
      rw [w.partition_unused_fiber l r hr,Finset.card_empty,Nat.zero_sub,fullZ_zero]
    _ = ∏ c : Fin k, fullZ Unit ((w.fiber (some c)).card-1) := by
      rw [Finset.prod_image]
      · simp only [w.partition_root_fiber l]
      · intro a _ b _ hab
        exact w.root_injective hab

end Dowling.OccupiedWord
