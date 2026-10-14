import MainTheorems.AHOConstants.Potential
import Mathlib.Data.Finset.Max

namespace ResearchMain.AHOConstants

open scoped BigOperators

variable {m : ℕ}

noncomputable def lowerEndpoint (p q : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : ℝ :=
  max (-cyclicPotential p q i) (q i - cyclicPotential p q i - 1 / 2)

noncomputable def upperEndpoint (p q : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : ℝ :=
  min (1 / 2 - cyclicPotential p q i) (q i - cyclicPotential p q i)

theorem feasible_iff_common_interval (p q : Fin (m + 1) → ℝ)
    (ht : (∑ i, p i) = ∑ i, q i) :
    Feasible p q ↔
      ∃ x : ℝ, ∀ i, lowerEndpoint p q i ≤ x ∧ x ≤ upperEndpoint p q i := by
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨a 0, fun i => ?_⟩
    have ha := h.affine i
    have hb := h.1 i
    have hq := h.2.1 i
    constructor
    · apply max_le <;> linarith
    · apply le_min <;> linarith
  · rintro ⟨x, hx⟩
    refine ⟨fun i => x + cyclicPotential p q i,
      fun i => q i - x - cyclicPotential p q i, ?_⟩
    constructor
    · intro i
      have hl := hx i
      change max _ _ ≤ x ∧ x ≤ min _ _ at hl
      have h₁ := le_of_max_le_left hl.1
      have h₂ := le_of_max_le_right hl.1
      have h₃ := le_of_le_min_left hl.2
      have h₄ := le_of_le_min_right hl.2
      constructor
      · linarith
      constructor
      · linarith
      constructor <;> linarith
    constructor
    · intro i
      ring
    · intro i
      have hc := cyclicPotential_step p q ht i
      linarith

theorem feasible_iff_interval_pairs (p q : Fin (m + 1) → ℝ)
    (ht : (∑ i, p i) = ∑ i, q i) :
    Feasible p q ↔ ∀ i j, lowerEndpoint p q i ≤ upperEndpoint p q j := by
  rw [feasible_iff_common_interval p q ht]
  constructor
  · rintro ⟨x, hx⟩ i j
    exact (hx i).1.trans (hx j).2
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
      (lowerEndpoint p q) ⟨0, Finset.mem_univ _⟩
    exact ⟨lowerEndpoint p q i, fun j => ⟨hi j (Finset.mem_univ _), h i j⟩⟩

theorem infeasible_interval_witness (p q : Fin (m + 1) → ℝ)
    (ht : (∑ i, p i) = ∑ i, q i) (h : ¬Feasible p q) :
    ∃ i j, upperEndpoint p q j < lowerEndpoint p q i := by
  rw [feasible_iff_interval_pairs p q ht] at h
  push Not at h
  exact h

theorem feasible_iff_scalar_bounds (p q : Fin (m + 1) → ℝ)
    (ht : (∑ i, p i) = ∑ i, q i) :
    Feasible p q ↔ ∀ i j,
      -cyclicPotential p q i ≤ 1 / 2 - cyclicPotential p q j ∧
      -cyclicPotential p q i ≤ q j - cyclicPotential p q j ∧
      q i - cyclicPotential p q i - 1 / 2 ≤ 1 / 2 - cyclicPotential p q j ∧
      q i - cyclicPotential p q i - 1 / 2 ≤ q j - cyclicPotential p q j := by
  rw [feasible_iff_interval_pairs p q ht]
  simp only [lowerEndpoint, upperEndpoint, max_le_iff, le_min_iff]
  constructor
  · intro h i j
    exact ⟨(h i j).1.1, (h i j).2.1, (h i j).1.2, (h i j).2.2⟩
  · intro h i j
    exact ⟨⟨(h i j).1, (h i j).2.2.1⟩, ⟨(h i j).2.1, (h i j).2.2.2⟩⟩

end ResearchMain.AHOConstants
