import MainTheorems.SIOrders
import Mathlib.Combinatorics.Matroid.IndepAxioms

namespace ResearchMain.SIBO

open scoped BigOperators

variable {E : Type*} [Fintype E]

theorem uniform_base_exchange (r : ℕ) : Matroid.ExchangeProperty (fun B : Set E => B.ncard = r) := by
  intro A B hA hB a ha
  have hnsub : ¬ B ⊆ A := by
    intro hs
    have heq : B = A := Set.eq_of_subset_of_ncard_le hs (by omega)
    exact ha.2 (heq ▸ ha.1)
  obtain ⟨b, hb, hba⟩ := Set.not_subset.mp hnsub
  refine ⟨b, ⟨hb, hba⟩, ?_⟩
  change (insert b (A \ {a})).ncard = r
  rw [Set.ncard_insert_of_notMem (fun h => hba h.1)]
  have hcard := Set.ncard_sdiff_singleton_add_one ha.1
  omega

noncomputable def uniformMatroid (r : ℕ) (hr : r ≤ Fintype.card E) : Matroid E :=
  Matroid.ofIsBaseOfFinite (Set.toFinite (Set.univ : Set E)) (fun B => B.ncard = r)
    (by
      obtain ⟨B, _, hB⟩ := Set.exists_subset_card_eq
        (show r ≤ (Set.univ : Set E).ncard by simpa [Nat.card_eq_fintype_card] using hr)
      exact ⟨B, hB⟩)
    (uniform_base_exchange r) (fun _ _ => Set.subset_univ _)

@[simp] theorem uniformMatroid_isBase {r : ℕ} (hr : r ≤ Fintype.card E) (B : Set E) :
    (uniformMatroid r hr).IsBase B ↔ B.ncard = r := Iff.rfl

namespace BasisOrders

variable [DecidableEq E] {A B : Finset E} (o : BasisOrders A B)

omit [Fintype E] in
theorem exchange_card (halign : ∀ i, o.a i ∈ B → o.a i = o.b i) (lo hi : ℕ) :
    (o.exchange lo hi).card = B.card := by
  classical
  let I := indexInterval o.n lo hi
  have hbsub : I.image o.b ⊆ B := by
    intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact o.b_mem i
  have hd : Disjoint (B \ I.image o.b) (I.image o.a) := by
    apply Finset.disjoint_left.mpr
    intro e he he'
    obtain ⟨heB, heI⟩ := Finset.mem_sdiff.mp he
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp he'
    exact heI (Finset.mem_image.mpr ⟨i, hiI, (halign i heB).symm⟩)
  have hib := Finset.card_image_of_injective I o.b_injective
  have hia := Finset.card_image_of_injective I o.a_injective
  have hle := Finset.card_le_card hbsub
  rw [exchange, Finset.card_union_of_disjoint hd, Finset.card_sdiff_of_subset hbsub, hib, hia]
  omega

end BasisOrders

end ResearchMain.SIBO
