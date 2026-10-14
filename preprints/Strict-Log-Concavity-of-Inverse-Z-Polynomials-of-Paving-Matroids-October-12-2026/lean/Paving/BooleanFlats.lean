import Paving.ActualInvariant
import ThagomizerTuran.BooleanEvaluation

namespace Paving
attribute [local instance] Classical.propDecidable
open MatroidInverseZ
variable {α : Type*} [Fintype α] {M : Matroid α}

omit [Fintype α] in
/-- Every subset of an actual independent flat remains a flat. -/
theorem indepFlat_subset_isFlat {F S : Set α} (hi : M.Indep F) (hF : M.IsFlat F)
    (hSF : S ⊆ F) : M.IsFlat S := by
  rw [M.isFlat_iff_closure_eq]
  have hc : M.closure S ⊆ F := by
    simpa only [hF.closure] using M.closure_subset_closure hSF
  have he := hi.closure_inter_eq_self_of_subset hSF
  rwa [Set.inter_eq_left.mpr hc] at he

noncomputable def independentFlatEmbedding (F : Set α) (hi : M.Indep F) (hF : M.IsFlat F) :
    Finset F ↪o MatroidInverseZ.Flat M where
  toFun A := ⟨Subtype.val '' (A : Set F), indepFlat_subset_isFlat hi hF (by
    rintro _ ⟨a, _, rfl⟩; exact a.property)⟩
  inj' := by
    intro A B h
    apply Finset.coe_injective
    exact Set.image_injective.mpr Subtype.val_injective (congrArg Subtype.val h)
  map_rel_iff' := by
    intro A B
    exact Set.image_subset_image_iff Subtype.val_injective

omit [Fintype α] in
theorem independentFlatEmbedding_rank (F : Set α) (hi : M.Indep F) (hF : M.IsFlat F)
    (A : Finset F) : MatroidInverseZ.flatRank M (independentFlatEmbedding F hi hF A) = A.card := by
  have hsub : Subtype.val '' (A : Set F) ⊆ F := by rintro _ ⟨a, _, rfl⟩; exact a.property
  change (M.eRk (Subtype.val '' (A : Set F))).toNat = A.card
  rw [(hi.subset hsub).eRk_eq_encard]
  change (Subtype.val '' (A : Set F)).ncard = A.card
  rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]

theorem independentFlatEmbedding_interval (F : Set α) (hi : M.Indep F) (hF : M.IsFlat F)
    (a b : Finset F) (y : MatroidInverseZ.Flat M)
    (_ha : independentFlatEmbedding F hi hF a ≤ y)
    (hb : y ≤ independentFlatEmbedding F hi hF b) :
    ∃ x, independentFlatEmbedding F hi hF x = y := by
  let x : Finset F := Finset.univ.filter (fun e => e.val ∈ y.val)
  refine ⟨x, Subtype.ext ?_⟩
  change Subtype.val '' (x : Set F) = y.val
  ext e
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (Finset.mem_filter.mp ha).2
  · intro he
    obtain ⟨a, _, ha⟩ := hb he
    have heF : e ∈ F := ha ▸ a.property
    exact ⟨⟨e, heF⟩, by simp [x, he], rfl⟩

theorem independentFlat_inverseKL (F : Set α) (hi : M.Indep F) (hF : M.IsFlat F)
    (a b : Finset F) (hab : a ⊆ b) :
    inverseKL (MatroidInverseZ.flatRank M)
      (independentFlatEmbedding F hi hF a) (independentFlatEmbedding F hi hF b) = 1 := by
  classical
  rw [inverseKL_interval_transport (independentFlatEmbedding F hi hF)
    (independentFlatEmbedding_interval F hi hF) Finset.card _ (by
      intro x y
      rw [independentFlatEmbedding_rank, independentFlatEmbedding_rank])]
  exact boolean_inverseKL a b hab

omit [Fintype α] in
@[simp] theorem independentFlatEmbedding_empty (F : Set α) (hi : M.Indep F) (hF : M.IsFlat F) :
    independentFlatEmbedding F hi hF ∅ = ⊥ := by
  apply Subtype.ext
  change Subtype.val '' (↑(∅ : Finset F) : Set F) = M.closure ∅
  have he := (indepFlat_subset_isFlat hi hF (Set.empty_subset F)).closure
  simpa using he.symm

@[simp] theorem independentFlatEmbedding_univ (F : Set α) (hi : M.Indep F) (hF : M.IsFlat F) :
    independentFlatEmbedding F hi hF Finset.univ = ⟨F, hF⟩ := by
  apply Subtype.ext
  change Subtype.val '' (↑(Finset.univ : Finset F) : Set F) = F
  simp

theorem actual_independentFlat_inverseKL (F : Set α) (hi : M.Indep F) (hF : M.IsFlat F) :
    inverseKL (MatroidInverseZ.flatRank M) ⊥ ⟨F,hF⟩ = 1 := by
  have h := independentFlat_inverseKL F hi hF ∅ Finset.univ (Finset.empty_subset _)
  simpa only [independentFlatEmbedding_empty, independentFlatEmbedding_univ] using h

theorem actual_independentFlat_mu (G : Set α) (hi : M.Indep G) (hG : M.IsFlat G)
    (F : MatroidInverseZ.Flat M) (hFG : F.1 ⊆ G) :
    IncidenceAlgebra.mu ℤ F ⟨G,hG⟩ = (-1 : ℤ)^(G.ncard-F.1.ncard) := by
  obtain ⟨a, ha⟩ := independentFlatEmbedding_interval G hi hG ∅ Finset.univ F
    (by rw [independentFlatEmbedding_empty]; exact bot_le)
    (by rw [independentFlatEmbedding_univ]; exact hFG)
  have hc : a.card = F.1.ncard := by
    have he := congrArg (fun G : MatroidInverseZ.Flat M => G.1.ncard) ha
    change (Subtype.val '' (a : Set G)).ncard = F.1.ncard at he
    simpa only [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset] using he
  have h := mu_interval_transport (independentFlatEmbedding G hi hG)
    (independentFlatEmbedding_interval G hi hG) a Finset.univ
  rw [boolean_mu _ _ (Finset.subset_univ _)] at h
  have hn : Fintype.card G = G.ncard := (Set.ncard_eq_toFinset_card' G).trans (Set.toFinset_card G) |>.symm
  simpa only [ha, independentFlatEmbedding_univ, Finset.card_univ, hn, hc] using h

end Paving
