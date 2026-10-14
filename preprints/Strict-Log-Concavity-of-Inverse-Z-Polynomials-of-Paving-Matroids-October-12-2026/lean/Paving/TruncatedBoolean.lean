import ThagomizerTuran.BooleanEvaluation
import Mathlib.Data.Nat.Choose.Sum

/-! Finite rank truncations of genuine Boolean subset lattices. These are the
uniform intervals occurring as restrictions to paving hyperplanes. -/
namespace Paving
attribute [local instance] Classical.propDecidable
open Finset MatroidInverseZ
variable (α : Type*) [Fintype α]

abbrev TruncatedFlat (r : ℕ) := {S : Finset α // S.card ≤ r ∨ S = univ}

noncomputable instance truncatedFintype (r : ℕ) : Fintype (TruncatedFlat α r) := Fintype.ofFinite _
noncomputable instance truncatedDecidableEq (r : ℕ) : DecidableEq (TruncatedFlat α r) := Classical.decEq _
noncomputable instance truncatedLFO (r : ℕ) : LocallyFiniteOrder (TruncatedFlat α r) := Fintype.toLocallyFiniteOrder

instance truncatedOrderBot (r : ℕ) : OrderBot (TruncatedFlat α r) where
  bot := ⟨∅, Or.inl (by simp)⟩
  bot_le _ := empty_subset _

instance truncatedOrderTop (r : ℕ) : OrderTop (TruncatedFlat α r) where
  top := ⟨univ, Or.inr rfl⟩
  le_top _ := subset_univ _

noncomputable def truncatedRank (r : ℕ) (F : TruncatedFlat α r) : ℕ := min (r+1) F.1.card

theorem truncated_proper_card (r : ℕ) (F : TruncatedFlat α r) (hF : F ≠ ⊤) : F.1.card ≤ r :=
  F.2.resolve_right (fun h => hF (Subtype.ext h))

theorem truncatedRank_proper (r : ℕ) (F : TruncatedFlat α r) (hF : F ≠ ⊤) :
    truncatedRank α r F = F.1.card := Nat.min_eq_right (by have := truncated_proper_card α r F hF; omega)

@[simp] theorem truncatedRank_bot (r : ℕ) : truncatedRank α r ⊥ = 0 := by
  change min (r+1) (∅ : Finset α).card = 0
  simp

@[simp] theorem truncatedRank_top (r : ℕ) (hr : r+1 ≤ Fintype.card α) :
    truncatedRank α r ⊤ = r+1 := by
  change min (r+1) (univ : Finset α).card = r+1
  simp only [card_univ]
  exact Nat.min_eq_left hr

theorem truncatedRank_strictMono (r : ℕ) : StrictMono (truncatedRank α r) := by
  intro F G hFG
  have hF : F ≠ ⊤ := fun h => by subst F; exact not_lt_of_ge le_top hFG
  have hc := Finset.card_lt_card (show F.1 ⊂ G.1 from hFG)
  rw [truncatedRank_proper α r F hF]
  unfold truncatedRank
  exact lt_min (by have := truncated_proper_card α r F hF; omega) hc

noncomputable def truncatedLowerEmbedding (r : ℕ) (F : Finset α) (hF : F.card ≤ r) :
    Finset {e // e ∈ F} ↪o TruncatedFlat α r where
  toFun A := ⟨A.image Subtype.val, Or.inl (le_trans (Finset.card_le_card (by
    intro e he
    obtain ⟨a, _, rfl⟩ := mem_image.mp he
    exact a.property)) hF)⟩
  inj' := by
    intro A B h
    exact Finset.image_injective Subtype.val_injective (congrArg Subtype.val h)
  map_rel_iff' := by intro A B; exact Finset.image_subset_image_iff Subtype.val_injective

theorem truncatedLowerEmbedding_rank (r : ℕ) (F : Finset α) (hF : F.card ≤ r)
    (A : Finset {e // e ∈ F}) : truncatedRank α r (truncatedLowerEmbedding α r F hF A) = A.card := by
  change min (r+1) (A.image Subtype.val).card = A.card
  rw [card_image_of_injective _ Subtype.val_injective]
  have hc : A.card ≤ F.card := by
    exact (Finset.card_le_card (Finset.subset_univ A)).trans_eq (by simp)
  exact Nat.min_eq_right (by omega)

theorem truncatedLowerEmbedding_interval (r : ℕ) (F : Finset α) (hF : F.card ≤ r)
    (a b : Finset {e // e ∈ F}) (y : TruncatedFlat α r)
    (_ha : truncatedLowerEmbedding α r F hF a ≤ y)
    (hb : y ≤ truncatedLowerEmbedding α r F hF b) :
    ∃ x, truncatedLowerEmbedding α r F hF x = y := by
  let x : Finset {e // e ∈ F} := univ.filter (fun e => e.val ∈ y.val)
  refine ⟨x, Subtype.ext ?_⟩
  change x.image Subtype.val = y.val
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := mem_image.mp he
    exact (mem_filter.mp ha).2
  · intro he
    obtain ⟨a, _, ha⟩ := mem_image.mp (hb he)
    have heF : e ∈ F := ha ▸ a.property
    exact mem_image.mpr ⟨⟨e, heF⟩, by simp [x, he], rfl⟩

end Paving
