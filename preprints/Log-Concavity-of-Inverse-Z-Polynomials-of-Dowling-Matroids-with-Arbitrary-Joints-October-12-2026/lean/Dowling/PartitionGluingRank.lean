import Dowling.PartitionGluingOrder
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section
namespace Dowling.GainPartition
open scoped Classical BigOperators
variable {G : Type*} [Group G] {n : ℕ}

theorem glue_isRoot_vertex (p : GainPartition G n)
    (q : ∀ c : Option (Fin n), GainPartition G (p.fiber c).card)
    (c : Option (Fin n)) (i : Fin (p.fiber c).card) :
    (p.glue q).IsRoot (p.fiberEmbedding c i) ↔ (q c).IsRoot i := by
  change p.glueCode q (p.fiberEmbedding c i) = some (p.fiberEmbedding c i,1) ↔
    (q c).code i = some (i,1)
  rw [glueCode_vertex]
  exact ⟨fun h => restrictionCode_map_injective (p.fiberEmbedding c) h,
    fun h => congrArg (Option.map _) h⟩

theorem sum_fiber_card (p : GainPartition G n) : (∑ c : Option (Fin n), (p.fiber c).card) = n := by
  have h := Fintype.card_congr p.fiberEquiv
  simpa only [Fintype.card_sigma,Fintype.card_fin] using h

theorem glue_roots_card (p : GainPartition G n)
    (q : ∀ c : Option (Fin n), GainPartition G (p.fiber c).card) :
    (p.glue q).roots.card = ∑ c : Option (Fin n), (q c).roots.card := by
  change (Finset.univ.filter (p.glue q).IsRoot).card = _
  rw [Finset.card_filter,← p.fiberEquiv.sum_comp,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  change (∑ i : Fin (p.fiber c).card, if (p.glue q).IsRoot (p.fiberEmbedding c i) then 1 else 0) = _
  simp only [glue_isRoot_vertex]
  exact (Finset.card_filter _ _).symm

theorem glue_rank (p : GainPartition G n)
    (q : ∀ c : Option (Fin n), GainPartition G (p.fiber c).card) :
    n-(p.glue q).roots.card = ∑ c : Option (Fin n), ((p.fiber c).card-(q c).roots.card) := by
  rw [glue_roots_card]
  calc
    _ = (∑ c : Option (Fin n), (p.fiber c).card) - ∑ c : Option (Fin n), (q c).roots.card :=
      congrArg (fun a => a-∑ c : Option (Fin n), (q c).roots.card) p.sum_fiber_card.symm
    _ = _ := (Finset.sum_tsub_distrib _ (fun c _ => (q c).roots_card_le)).symm

end Dowling.GainPartition
