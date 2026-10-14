import Paving.TruncatedBoolean
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

namespace Paving
attribute [local instance] Classical.propDecidable
open Finset MatroidInverseZ
variable {α : Type*} [Fintype α]

@[simp] theorem truncatedLowerEmbedding_empty (r : ℕ) (F : Finset α) (hF : F.card ≤ r) :
    truncatedLowerEmbedding α r F hF ∅ = ⊥ := by
  apply Subtype.ext
  change (∅ : Finset {e // e ∈ F}).image Subtype.val = ∅
  simp only [Finset.image_empty]

@[simp] theorem truncatedLowerEmbedding_univ (r : ℕ) (F : Finset α) (hF : F.card ≤ r) :
    truncatedLowerEmbedding α r F hF univ = ⟨F, Or.inl hF⟩ := by
  apply Subtype.ext
  change univ.image Subtype.val = F
  ext e
  simp

theorem truncated_mu_proper (r : ℕ) (F : TruncatedFlat α r) (hF : F ≠ ⊤) :
    IncidenceAlgebra.mu ℤ (⊥ : TruncatedFlat α r) F = (-1 : ℤ)^F.1.card := by
  have hc := truncated_proper_card α r F hF
  have h := mu_interval_transport (truncatedLowerEmbedding α r F.1 hc)
    (truncatedLowerEmbedding_interval α r F.1 hc) ∅ univ
  rw [boolean_mu _ _ (empty_subset _)] at h
  simpa only [truncatedLowerEmbedding_empty, truncatedLowerEmbedding_univ,
    card_empty, Nat.sub_zero, card_univ, Fintype.card_coe] using h

theorem truncated_inverseKL_proper (r : ℕ) (F : TruncatedFlat α r) (hF : F ≠ ⊤) :
    inverseKL (truncatedRank α r) ⊥ F = 1 := by
  have hc := truncated_proper_card α r F hF
  have h := inverseKL_interval_transport (truncatedLowerEmbedding α r F.1 hc)
    (truncatedLowerEmbedding_interval α r F.1 hc) Finset.card (truncatedRank α r)
    (by intro a b; rw [truncatedLowerEmbedding_rank, truncatedLowerEmbedding_rank]) ∅ univ
  rw [boolean_inverseKL _ _ (empty_subset _)] at h
  simpa only [truncatedLowerEmbedding_empty, truncatedLowerEmbedding_univ] using h

theorem subset_sum_card {R : Type*} [Semiring R] (w : ℕ → R) :
    (∑ I : Finset α, w I.card) =
      ∑ k ∈ range (Fintype.card α+1), (Fintype.card α).choose k * w k := by
  classical
  rw [← Finset.powerset_univ, Finset.sum_powerset]
  simp only [Finset.sum_powersetCard, card_univ, nsmul_eq_mul]

/-- Counting all proper truncated flats by their genuine subset cardinalities. -/
theorem truncated_proper_sum (r : ℕ) (hr : r+1 ≤ Fintype.card α) (w : ℕ → ℤ) :
    (∑ F ∈ Ico (⊥ : TruncatedFlat α r) ⊤, w F.1.card) =
      ∑ k ∈ range (r+1), (Fintype.card α).choose k * w k := by
  classical
  have hs : (∑ F ∈ Ico (⊥ : TruncatedFlat α r) ⊤, w F.1.card) =
      ∑ S ∈ (univ : Finset (Finset α)).filter (fun S => S.card ≤ r), w S.card := by
    apply sum_bij (fun F _ => F.1)
    · intro F hF
      exact mem_filter.mpr ⟨mem_univ _, truncated_proper_card α r F (mem_Ico.mp hF).2.ne⟩
    · intro F _ G _ he
      exact Subtype.ext he
    · intro S hS
      have hc := (mem_filter.mp hS).2
      refine ⟨⟨S, Or.inl hc⟩, mem_Ico.mpr ⟨bot_le, ?_⟩, rfl⟩
      apply lt_of_le_of_ne le_top
      intro he
      have hval := congrArg Subtype.val he
      change S = univ at hval
      rw [hval, card_univ] at hc
      omega
    · intro F _
      rfl
  rw [hs, sum_filter, subset_sum_card (fun k => if k ≤ r then w k else 0)]
  simp_rw [mul_ite, mul_zero]
  apply (sum_subset (by intro k hk; exact mem_range.mpr (by have := mem_range.mp hk; omega)) ?_).symm.trans
    (sum_congr rfl (fun k hk => by rw [ite_eq_left (by have := mem_range.mp hk; omega)]))
  intro k hk hnot
  have hn : ¬k ≤ r := by simpa only [mem_range, Nat.lt_succ_iff] using hnot
  exact ite_eq_right hn

/-- The genuine Möbius invariant of the rank-(r+1) uniform subset lattice. -/
theorem truncated_mu (r : ℕ) (hr : r+1 ≤ Fintype.card α) :
    IncidenceAlgebra.mu ℤ (⊥ : TruncatedFlat α r) ⊤ =
      (-1 : ℤ)^(r+1) * (Fintype.card α-1).choose r := by
  have hne : (⊥ : TruncatedFlat α r) ≠ ⊤ := by
    intro h
    have he := congrArg (fun F : TruncatedFlat α r => F.1.card) h
    change (∅ : Finset α).card = univ.card at he
    simp only [card_empty, card_univ] at he
    omega
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hne]
  have he : (∑ F ∈ Ico (⊥ : TruncatedFlat α r) ⊤,
      IncidenceAlgebra.mu ℤ (⊥ : TruncatedFlat α r) F) =
      ∑ F ∈ Ico (⊥ : TruncatedFlat α r) ⊤, (-1 : ℤ)^F.1.card := by
    apply sum_congr rfl
    intro F hF
    exact truncated_mu_proper r F (mem_Ico.mp hF).2.ne
  rw [he, truncated_proper_sum r hr]
  have hc : Fintype.card α = (Fintype.card α-1)+1 := by omega
  simp_rw [mul_comm ((Fintype.card α).choose _ : ℤ)]
  rw [hc, Int.alternating_sum_range_choose_eq_choose]
  simp only [Nat.add_sub_cancel, pow_succ]
  ring

end Paving
