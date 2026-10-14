import Paving.Hyperplanes
import Paving.BooleanFlats
import Paving.UniformCoefficients

namespace Paving
attribute [local instance] Classical.propDecidable
open Finset MatroidInverseZ
variable {α : Type*} [Fintype α] {M : Matroid α}

theorem subsetRank_le_card (M : Matroid α) (S : Set α) : subsetRank M S ≤ S.ncard :=
  ENat.toNat_le_toNat (M.eRk_le_encard S) (Set.toFinite S).encard_lt_top.ne

theorem hyperplane_card_lower {H : Set α} (hH : IsHyperplane M H) : rank M ≤ H.ncard+1 := by
  have h := subsetRank_le_card M H
  have hh := hH.2
  omega

theorem IsPaving.flat_below_hyperplane_card (hM : IsPaving M)
    {H F : Set α} (hH : IsHyperplane M H) (hF : M.IsFlat F) (hFH : F ⊂ H) :
    F.ncard+2 ≤ rank M := by
  have hr := flat_subsetRank_strict hF hH.1 hFH
  have hh := hH.2
  have hi := hM.flat_indep_of_rank hF (by omega)
  have hc : subsetRank M F = F.ncard := congrArg ENat.toNat hi.eRk_eq_encard
  omega

noncomputable def hyperplaneEmbedding (hM : IsPaving M) (d : ℕ) (hr : rank M=d+2)
    (H : Set α) (hH : IsHyperplane M H) : TruncatedFlat H d ↪o MatroidInverseZ.Flat M where
  toFun A := ⟨Subtype.val '' (A.1 : Set H), by
    rcases A.2 with hA | hA
    · apply hM.small_set_isFlat
      · rintro _ ⟨a, _, rfl⟩
        exact hH.1.subset_ground a.property
      · rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
        omega
    · simpa only [hA, Finset.coe_univ, Set.image_univ, Subtype.range_coe_subtype,
        Set.ofPred_mem_eq] using hH.1⟩
  inj' := by
    intro A B he
    apply Subtype.ext
    apply Finset.coe_injective
    exact Set.image_injective.mpr Subtype.val_injective (congrArg Subtype.val he)
  map_rel_iff' := by intro A B; exact Set.image_subset_image_iff Subtype.val_injective

@[simp] theorem hyperplaneEmbedding_top (hM : IsPaving M) (d : ℕ) (hr : rank M=d+2)
    (H : Set α) (hH : IsHyperplane M H) : hyperplaneEmbedding hM d hr H hH ⊤ = ⟨H,hH.1⟩ := by
  apply Subtype.ext
  change Subtype.val '' (↑(univ : Finset H) : Set H) = H
  simp

@[simp] theorem hyperplaneEmbedding_bot (hM : IsPaving M) (d : ℕ) (hr : rank M=d+2)
    (H : Set α) (hH : IsHyperplane M H) : hyperplaneEmbedding hM d hr H hH ⊥ = ⊥ := by
  apply Subtype.ext
  change Subtype.val '' (↑(∅ : Finset H) : Set H) = M.closure ∅
  have he := (hM.small_set_isFlat (Set.empty_subset _) (by simp only [Set.ncard_empty]; omega)).closure
  simpa using he.symm

theorem hyperplaneEmbedding_rank (hM : IsPaving M) (d : ℕ) (hr : rank M=d+2)
    (H : Set α) (hH : IsHyperplane M H) (A : TruncatedFlat H d) :
    MatroidInverseZ.flatRank M (hyperplaneEmbedding hM d hr H hH A) = truncatedRank H d A := by
  by_cases htop : A = ⊤
  · subst A
    rw [hyperplaneEmbedding_top, truncatedRank_top H d]
    · change subsetRank M H = d+1
      have hh := hH.2
      omega
    · have hc := hyperplane_card_lower hH
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card] at hc
      omega
  · rw [truncatedRank_proper H d A htop]
    have hc := truncated_proper_card H d A htop
    change (M.eRk (Subtype.val '' (A.1 : Set H))).toNat = A.1.card
    rw [hM.small_set_rank (by rintro _ ⟨a, _, rfl⟩; exact hH.1.subset_ground a.property)]
    · rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
    · rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
      omega

theorem hyperplaneEmbedding_interval (hM : IsPaving M) (d : ℕ) (hr : rank M=d+2)
    (H : Set α) (hH : IsHyperplane M H) (a b : TruncatedFlat H d)
    (y : MatroidInverseZ.Flat M) (_ha : hyperplaneEmbedding hM d hr H hH a ≤ y)
    (hb : y ≤ hyperplaneEmbedding hM d hr H hH b) :
    ∃ x, hyperplaneEmbedding hM d hr H hH x = y := by
  let A : Finset H := univ.filter (fun e => e.val ∈ y.val)
  have hyH : y.1 ⊆ H := by
    intro e he
    obtain ⟨a, _, ha⟩ := hb he
    exact ha ▸ a.property
  have he : Subtype.val '' (A : Set H) = y.1 := by
    ext e
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (mem_filter.mp ha).2
    · intro he
      exact ⟨⟨e, hyH he⟩, by simp [A,he], rfl⟩
  have hA : A.card ≤ d ∨ A = univ := by
    by_cases hyt : y.1 = H
    · right
      ext a
      simp [A,hyt]
    · left
      have hc := hM.flat_below_hyperplane_card hH y.2
        (show y.1 ⊂ H from ⟨hyH, fun h => hyt (Set.Subset.antisymm hyH h)⟩)
      have hcard : A.card = y.1.ncard := by
        rw [← he, Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
      omega
  exact ⟨⟨A,hA⟩, Subtype.ext he⟩

/-- Hyperplane restrictions are genuine uniform ranked flat intervals. -/
theorem hyperplane_inverseKL (hM : IsPaving M) (d : ℕ) (hr : rank M=d+2)
    (H : Set α) (hH : IsHyperplane M H) :
    inverseKL (MatroidInverseZ.flatRank M) ⊥ ⟨H,hH.1⟩ = uniformQ (α:=H) d := by
  have h := inverseKL_interval_transport (hyperplaneEmbedding hM d hr H hH)
    (hyperplaneEmbedding_interval hM d hr H hH) (truncatedRank H d) (MatroidInverseZ.flatRank M)
    (by intro a b; rw [hyperplaneEmbedding_rank, hyperplaneEmbedding_rank]) ⊥ ⊤
  simpa only [hyperplaneEmbedding_bot, hyperplaneEmbedding_top, uniformQ] using h

theorem hyperplane_mu (hM : IsPaving M) (d : ℕ) (hr : rank M=d+2)
    (H : Set α) (hH : IsHyperplane M H) :
    IncidenceAlgebra.mu ℤ (⊥ : MatroidInverseZ.Flat M) ⟨H,hH.1⟩ =
      (-1 : ℤ)^(d+1) * (H.ncard-1).choose d := by
  have hn : Fintype.card H = H.ncard := (Set.ncard_eq_toFinset_card' H).trans (Set.toFinset_card H) |>.symm
  have hc := hyperplane_card_lower hH
  have h := mu_interval_transport (hyperplaneEmbedding hM d hr H hH)
    (hyperplaneEmbedding_interval hM d hr H hH) ⊥ ⊤
  rw [truncated_mu d (by rw [hn]; omega)] at h
  simpa only [hyperplaneEmbedding_bot, hyperplaneEmbedding_top, hn] using h

/-- The upper Möbius factor inside each actual paving hyperplane. -/
theorem hyperplane_upper_mu (hM : IsPaving M) (d : ℕ) (hr : rank M=d+2)
    (H : Set α) (hH : IsHyperplane M H) (F : MatroidInverseZ.Flat M)
    (hFH : F.1 ⊆ H) (hne : F.1 ≠ H) :
    IncidenceAlgebra.mu ℤ F ⟨H,hH.1⟩ =
      (-1 : ℤ)^(d-F.1.ncard+1) * (H.ncard-F.1.ncard-1).choose (d-F.1.ncard) := by
  have hn : Fintype.card H = H.ncard := (Set.ncard_eq_toFinset_card' H).trans (Set.toFinset_card H) |>.symm
  obtain ⟨x, hx⟩ := hyperplaneEmbedding_interval hM d hr H hH ⊥ ⊤ F
    (by rw [hyperplaneEmbedding_bot]; exact bot_le)
    (by rw [hyperplaneEmbedding_top]; exact hFH)
  have hxt : x ≠ ⊤ := by
    intro he
    rw [he, hyperplaneEmbedding_top] at hx
    exact hne (congrArg Subtype.val hx).symm
  have hxc := truncated_proper_card H d x hxt
  have hc : x.1.card = F.1.ncard := by
    have he := congrArg (fun G : MatroidInverseZ.Flat M => G.1.ncard) hx
    change (Subtype.val '' (x.1 : Set H)).ncard = F.1.ncard at he
    simpa only [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset] using he
  have h := mu_interval_transport (hyperplaneEmbedding hM d hr H hH)
    (hyperplaneEmbedding_interval hM d hr H hH) x ⊤
  have ht := truncated_upper_mu d (by rw [hn]; have := hyperplane_card_lower hH; omega) x.1 hxc
  change IncidenceAlgebra.mu ℤ x ⊤ = _ at ht
  rw [ht] at h
  simpa only [hx, hyperplaneEmbedding_top, hn, hc] using h

end Paving
