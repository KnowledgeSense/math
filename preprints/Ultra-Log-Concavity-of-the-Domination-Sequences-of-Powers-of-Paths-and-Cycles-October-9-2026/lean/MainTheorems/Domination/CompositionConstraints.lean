import MainTheorems.Domination.CompositionPositions
import MainTheorems.Domination.CycleCoverage

namespace ResearchMain.Domination

def pathBounds (r ℓ : ℕ) (i : Fin r) : ℕ :=
  if i.val = 0 ∨ i.val + 1 = r then ℓ + 1 else 2 * ℓ + 1

theorem pathBounds_pos (r ℓ : ℕ) (i : Fin r) : 1 ≤ pathBounds r ℓ i := by
  unfold pathBounds
  split <;> omega

theorem composition_path_constraints {n k ℓ : ℕ} (c : Composition (n + 1))
    (hlen : c.length = k + 2) :
    Dominates (pathPower n ℓ) (selectedVertices c) ↔
      c.blocksFun ⟨0, by omega⟩ ≤ ℓ + 1 ∧
        c.blocksFun ⟨k + 1, by omega⟩ ≤ ℓ + 1 ∧
          ∀ i : Fin k, c.blocksFun ⟨i.val + 1, by have := i.isLt; omega⟩ ≤ 2 * ℓ + 1 := by
  rw [selectedVertices_image c hlen,
    path_gap_criterion _ (compositionPositions_strictMono c hlen)]
  have hfirst := compositionPositions_first c hlen
  have hfirstPos := c.one_le_blocksFun ⟨0, by omega⟩
  have hlast := compositionPositions_last c hlen
  have hlastBound := (compositionPositions c hlen (Fin.last k)).isLt
  constructor
  · rintro ⟨hf, hl, hg⟩
    refine ⟨by omega, by omega, ?_⟩
    intro i
    have hstep := compositionPositions_step c hlen i
    have hgap := hg i
    omega
  · rintro ⟨hf, hl, hg⟩
    refine ⟨by omega, by omega, ?_⟩
    intro i
    have hstep := compositionPositions_step c hlen i
    have hgap := hg i
    omega

theorem pathBounds_constraints {n k ℓ : ℕ} (c : Composition (n + 1))
    (hlen : c.length = k + 2) :
    (∀ i, c.blocksFun i ≤ pathBounds c.length ℓ i) ↔
      c.blocksFun ⟨0, by omega⟩ ≤ ℓ + 1 ∧
        c.blocksFun ⟨k + 1, by omega⟩ ≤ ℓ + 1 ∧
          ∀ i : Fin k, c.blocksFun ⟨i.val + 1, by have := i.isLt; omega⟩ ≤ 2 * ℓ + 1 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa only [pathBounds, zero_add, true_or, ite_true] using h ⟨0, by omega⟩
    · simpa [pathBounds, hlen] using h ⟨k + 1, by omega⟩
    · intro i
      have hi0 : i.val + 1 ≠ 0 := by omega
      have hilast : i.val + 1 + 1 ≠ c.length := by have := i.isLt; omega
      simpa only [pathBounds, hi0, hilast, false_or, ite_false] using
        h ⟨i.val + 1, by have := i.isLt; omega⟩
  · rintro ⟨hf, hl, hg⟩ j
    by_cases hj0 : j.val = 0
    · have hj : j = ⟨0, by omega⟩ := Fin.ext hj0
      rw [hj]
      simpa only [pathBounds, zero_add, true_or, ite_true] using hf
    · by_cases hjlast : j.val + 1 = c.length
      · have hj : j = ⟨k + 1, by omega⟩ := by
          apply Fin.ext
          change j.val = k + 1
          omega
        rw [hj]
        simpa [pathBounds, hlen] using hl
      · let i : Fin k := ⟨j.val - 1, by have := j.isLt; omega⟩
        have hidx : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin c.length) = j := by
          apply Fin.ext
          change j.val - 1 + 1 = j.val
          omega
        have h := hg i
        rw [hidx] at h
        simpa only [pathBounds, hj0, hjlast, false_or, ite_false] using h

theorem composition_path_bounds {n k ℓ : ℕ} (c : Composition (n + 1))
    (hlen : c.length = k + 2) :
    Dominates (pathPower n ℓ) (selectedVertices c) ↔
      ∀ i, c.blocksFun i ≤ pathBounds c.length ℓ i := by
  rw [composition_path_constraints c hlen, pathBounds_constraints c hlen]

theorem composition_cycle_constraints {n k ℓ : ℕ} (c : Composition (n + 1))
    (hlen : c.length = k + 2) :
    Dominates (cyclePower n ℓ) (selectedVertices c) ↔
      c.blocksFun ⟨0, by omega⟩ + c.blocksFun ⟨k + 1, by omega⟩ ≤ 2 * ℓ + 2 ∧
        ∀ i : Fin k, c.blocksFun ⟨i.val + 1, by have := i.isLt; omega⟩ ≤ 2 * ℓ + 1 := by
  rw [selectedVertices_image c hlen,
    cycle_gap_criterion _ (compositionPositions_strictMono c hlen)]
  have hfirst := compositionPositions_first c hlen
  have hfirstPos := c.one_le_blocksFun ⟨0, by omega⟩
  have hlast := compositionPositions_last c hlen
  have hlastBound := (compositionPositions c hlen (Fin.last k)).isLt
  constructor
  · rintro ⟨hw, hg⟩
    refine ⟨by omega, ?_⟩
    intro i
    have hstep := compositionPositions_step c hlen i
    have hgap := hg i
    omega
  · rintro ⟨hw, hg⟩
    refine ⟨by omega, ?_⟩
    intro i
    have hstep := compositionPositions_step c hlen i
    have hgap := hg i
    omega

end ResearchMain.Domination
