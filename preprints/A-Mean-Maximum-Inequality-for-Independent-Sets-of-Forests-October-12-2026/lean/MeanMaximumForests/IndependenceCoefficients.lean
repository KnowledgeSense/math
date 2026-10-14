import MeanMaximumForests.GraphInvariants
namespace MeanMaximumForests
open Finset
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- Coefficients of the independence polynomial on a finite vertex set. -/
noncomputable def independentSetCoefficient (s : Finset V) (k : ℕ) : ℕ := by
  classical
  exact ((independentSetsWithin G s).filter (fun t => t.card = k)).card

omit [DecidableEq V] in
theorem coefficient_pos_iff (s : Finset V) (k : ℕ) :
    0 < independentSetCoefficient G s k ↔
      ∃ t, t ⊆ s ∧ Independent G t ∧ t.card = k := by
  classical
  simp only [independentSetCoefficient, card_pos, filter_nonempty_iff, mem_independentSetsWithin]
  constructor
  · rintro ⟨t, ⟨ht, hi⟩, he⟩
    exact ⟨t, ht, hi, he⟩
  · rintro ⟨t, ht, hi, he⟩
    exact ⟨t, ⟨ht, hi⟩, he⟩

omit [DecidableEq V] in
theorem coefficient_pos_iff_le (s : Finset V) (k : ℕ) :
    0 < independentSetCoefficient G s k ↔ k ≤ independenceNumber G s := by
  rw [coefficient_pos_iff]
  constructor
  · rintro ⟨t, ht, hi, rfl⟩
    exact independent_card_le G s ht hi
  · intro hk
    obtain ⟨t, ht, hi, he⟩ := exists_maximum_independentSet G s
    obtain ⟨u, hu, hc⟩ := exists_subset_card_eq (he ▸ hk)
    exact ⟨u, hu.trans ht, hi.mono G hu, hc⟩

@[simp] theorem coefficient_zero (s : Finset V) : independentSetCoefficient G s 0 = 1 := by
  classical
  have he : (independentSetsWithin G s).filter (fun t => t.card = 0) = {∅} := by
    ext t
    simp only [mem_filter, mem_independentSetsWithin, card_eq_zero, mem_singleton]
    constructor
    · rintro ⟨_, rfl⟩
      rfl
    · rintro rfl
      exact ⟨⟨empty_subset _, independent_empty G⟩, rfl⟩
  simp only [independentSetCoefficient, he, card_singleton]

omit [DecidableEq V] in
theorem coefficient_eq_zero_of_gt (s : Finset V) (k : ℕ)
    (h : independenceNumber G s < k) : independentSetCoefficient G s k = 0 := by
  apply Nat.eq_zero_of_not_pos
  rw [coefficient_pos_iff_le]
  exact not_le.mpr h
end MeanMaximumForests
