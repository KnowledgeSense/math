import MainTheorems.Domination.PathCounts
import MainTheorems.Domination.CompositionMoments

namespace ResearchMain.Domination

open Classical

set_option maxHeartbeats 1000000

noncomputable def cycleParts (n k m : ℕ) : Finset (Fin (k + 2) → ℕ) :=
  ((boundedParts (fun _ : Fin (k + 2) => m)).filter (fun p => ∑ i, p i = n + 1)).filter
    (fun p => p 0 + p (Fin.last (k + 1)) ≤ m + 1)

theorem composition_cycle_fixedParts {n k ℓ : ℕ} (c : Composition (n + 1))
    (hlen : c.length = k + 2) :
    Dominates (cyclePower n ℓ) (selectedVertices c) ↔
      fixedParts c hlen 0 + fixedParts c hlen (Fin.last (k + 1)) ≤ 2 * ℓ + 2 ∧
        ∀ i : Fin k, fixedParts c hlen i.succ.castSucc ≤ 2 * ℓ + 1 := by
  rw [composition_cycle_constraints c hlen]
  rfl

theorem dominationCount_cyclePower (n k ℓ : ℕ) :
    dominationCount (cyclePower n ℓ) (k + 1) = (cycleParts n k (2 * ℓ + 1)).card := by
  classical
  symm
  unfold dominationCount
  apply Finset.card_bij (fun p hp => selectedVertices
    (boundedComposition (fun _ : Fin (k + 2) => 2 * ℓ + 1) p (Finset.mem_filter.mp hp).1))
  · intro p hp
    obtain ⟨hpsum, hend⟩ := Finset.mem_filter.mp hp
    let c := boundedComposition (fun _ : Fin (k + 2) => 2 * ℓ + 1) p hpsum
    have hlen : c.length = k + 2 := boundedComposition_length _ _ _
    have hparts : fixedParts c hlen = p :=
      fixedParts_eq_of_blocks c p hlen (boundedComposition_blocks _ _ _)
    apply (mem_dominatingSets _ _ _).mpr
    constructor
    · change (selectedVertices c).card = k + 1
      have hc := selectedVertices_card c
      omega
    · apply (composition_cycle_fixedParts c hlen).mpr
      rw [hparts]
      refine ⟨by omega, ?_⟩
      intro i
      exact ((mem_boundedParts _ p).mp (Finset.mem_filter.mp hpsum).1 i.succ.castSucc).2
  · intro p hp q hq heq
    have hc : boundedComposition (fun _ : Fin (k + 2) => 2 * ℓ + 1) p
        (Finset.mem_filter.mp hp).1 =
        boundedComposition (fun _ : Fin (k + 2) => 2 * ℓ + 1) q
          (Finset.mem_filter.mp hq).1 := (compositionSetEquiv n).injective heq
    have hblocks := congrArg Composition.blocks hc
    unfold boundedComposition at hblocks
    change List.ofFn p = List.ofFn q at hblocks
    exact List.ofFn_inj.mp hblocks
  · intro S hS
    obtain ⟨hcard, hdom⟩ := (mem_dominatingSets _ _ _).mp hS
    let c := (compositionSetEquiv n).symm S
    have hselected : selectedVertices c = S := (compositionSetEquiv n).apply_symm_apply S
    have hlen : c.length = k + 2 := by
      have hc := selectedVertices_card c
      rw [hselected, hcard] at hc
      omega
    let p := fixedParts c hlen
    have hpPos : ∀ i, 1 ≤ p i := fun i => c.one_le_blocksFun (Fin.cast hlen.symm i)
    have hconstraints : p 0 + p (Fin.last (k + 1)) ≤ 2 * ℓ + 2 ∧
        ∀ i : Fin k, p i.succ.castSucc ≤ 2 * ℓ + 1 := by
      apply (composition_cycle_fixedParts c hlen).mp
      rw [hselected]
      exact hdom
    have hpSum : ∑ i, p i = n + 1 := fixedParts_sum c hlen
    have hpBound : ∀ i, p i ≤ 2 * ℓ + 1 := by
      intro i
      by_cases hi0 : i = 0
      · rw [hi0]
        have h := hpPos (Fin.last (k + 1))
        omega
      · by_cases hilast : i = Fin.last (k + 1)
        · rw [hilast]
          have h := hpPos 0
          omega
        · have hi := i.isLt
          have hv0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
          have hvl : i.val ≠ k + 1 := fun h => hilast (Fin.ext h)
          let j : Fin k := ⟨i.val - 1, by omega⟩
          have heq : j.succ.castSucc = i := by
            apply Fin.ext
            change i.val - 1 + 1 = i.val
            omega
          simpa only [heq] using hconstraints.2 j
    have hp : p ∈ cycleParts n k (2 * ℓ + 1) := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        refine ⟨(mem_boundedParts _ _).mpr (fun i => ⟨hpPos i, hpBound i⟩), hpSum⟩
      · exact hconstraints.1
    refine ⟨p, hp, ?_⟩
    unfold boundedComposition
    change selectedVertices (compositionOfParts (fixedParts c hlen) _ _) = S
    rw [compositionOfParts_fixedParts]
    exact hselected

end ResearchMain.Domination
