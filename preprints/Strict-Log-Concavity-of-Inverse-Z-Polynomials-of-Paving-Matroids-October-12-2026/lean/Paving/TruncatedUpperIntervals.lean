import Paving.TruncatedEvaluation

namespace Paving
attribute [local instance] Classical.propDecidable
open Finset MatroidInverseZ
variable {α : Type*} [Fintype α]

noncomputable def adjoinFixed (F : Finset α) (A : Finset {e // e ∉ F}) : Finset α :=
  F ∪ A.image Subtype.val

omit [Fintype α] in
theorem adjoinFixed_card (F : Finset α) (A : Finset {e // e ∉ F}) :
    (adjoinFixed F A).card = F.card + A.card := by
  classical
  unfold adjoinFixed
  rw [card_union_of_disjoint, card_image_of_injective _ Subtype.val_injective]
  apply disjoint_left.mpr
  intro e he ha
  obtain ⟨a, _, rfl⟩ := mem_image.mp ha
  exact a.property he

omit [Fintype α] in
@[simp] theorem adjoinFixed_empty (F : Finset α) : adjoinFixed F ∅ = F := by
  classical
  simp [adjoinFixed]

@[simp] theorem adjoinFixed_univ (F : Finset α) : adjoinFixed F univ = univ := by
  classical
  ext e
  simp only [adjoinFixed, mem_union, mem_image, mem_univ, true_and, iff_true]
  by_cases h : e ∈ F
  · exact Or.inl h
  · exact Or.inr ⟨⟨e,h⟩, rfl⟩

omit [Fintype α] in
theorem adjoinFixed_le_iff (F : Finset α) (A B : Finset {e // e ∉ F}) :
    adjoinFixed F A ⊆ adjoinFixed F B ↔ A ⊆ B := by
  classical
  constructor
  · intro h a ha
    have hm := h (mem_union_right F (mem_image.mpr ⟨a, ha, rfl⟩))
    have hi := (mem_union.mp hm).resolve_left a.property
    obtain ⟨b, hb, he⟩ := mem_image.mp hi
    have he' : b = a := Subtype.val_injective he
    exact he' ▸ hb
  · intro h
    exact union_subset_union (subset_refl _) (image_subset_image h)

noncomputable def truncatedUpperEmbedding (r : ℕ) (F : Finset α) (hF : F.card ≤ r) :
    TruncatedFlat {e // e ∉ F} (r-F.card) ↪o TruncatedFlat α r where
  toFun A := ⟨adjoinFixed F A.1, by
    rcases A.2 with hA | hA
    · left
      rw [adjoinFixed_card]
      omega
    · right
      rw [hA, adjoinFixed_univ]⟩
  inj' := by
    intro A B h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    exact Subset.antisymm ((adjoinFixed_le_iff F A.1 B.1).mp he.le)
      ((adjoinFixed_le_iff F B.1 A.1).mp he.ge)
  map_rel_iff' := by intro A B; exact adjoinFixed_le_iff F A.1 B.1

theorem truncatedUpperEmbedding_interval (r : ℕ) (F : Finset α) (hF : F.card ≤ r)
    (a b : TruncatedFlat {e // e ∉ F} (r-F.card)) (y : TruncatedFlat α r)
    (ha : truncatedUpperEmbedding r F hF a ≤ y)
    (_hb : y ≤ truncatedUpperEmbedding r F hF b) :
    ∃ x, truncatedUpperEmbedding r F hF x = y := by
  classical
  let A : Finset {e // e ∉ F} := univ.filter (fun e => e.val ∈ y.val)
  have hFy : F ⊆ y.1 := (subset_union_left : F ⊆ adjoinFixed F a.1).trans ha
  have he : adjoinFixed F A = y.1 := by
    ext e
    simp only [adjoinFixed, mem_union, mem_image]
    constructor
    · rintro (he | ⟨a, ha, rfl⟩)
      · exact hFy he
      · exact (mem_filter.mp ha).2
    · intro hey
      by_cases heF : e ∈ F
      · exact Or.inl heF
      · exact Or.inr ⟨⟨e,heF⟩, by simp [A,hey], rfl⟩
  have hA : A.card ≤ r-F.card ∨ A = univ := by
    rcases y.2 with hy | hy
    · left
      have hc := adjoinFixed_card F A
      rw [he] at hc
      omega
    · right
      ext e
      simp [A,hy]
  exact ⟨⟨A,hA⟩, Subtype.ext he⟩

@[simp] theorem truncatedUpperEmbedding_bot (r : ℕ) (F : Finset α) (hF : F.card ≤ r) :
    truncatedUpperEmbedding r F hF ⊥ = ⟨F, Or.inl hF⟩ := by
  apply Subtype.ext
  exact adjoinFixed_empty F

@[simp] theorem truncatedUpperEmbedding_top (r : ℕ) (F : Finset α) (hF : F.card ≤ r) :
    truncatedUpperEmbedding r F hF ⊤ = ⊤ := by
  apply Subtype.ext
  exact adjoinFixed_univ F

/-- Every actual upper uniform interval has its expected signed binomial Möbius value. -/
theorem truncated_upper_mu (r : ℕ) (hr : r+1 ≤ Fintype.card α)
    (F : Finset α) (hF : F.card ≤ r) :
    IncidenceAlgebra.mu ℤ (⟨F, Or.inl hF⟩ : TruncatedFlat α r) ⊤ =
      (-1 : ℤ)^(r-F.card+1) * (Fintype.card α-F.card-1).choose (r-F.card) := by
  have hn : Fintype.card {e // e ∉ F} = Fintype.card α-F.card := by
    simp [Fintype.card_subtype_compl]
  have h := mu_interval_transport (truncatedUpperEmbedding r F hF)
    (truncatedUpperEmbedding_interval r F hF) ⊥ ⊤
  rw [truncated_mu (r-F.card) (by rw [hn]; omega)] at h
  simpa only [truncatedUpperEmbedding_bot, truncatedUpperEmbedding_top, hn] using h

end Paving
