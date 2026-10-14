import MainTheorems.Domination.FixedCompositions
import MainTheorems.Domination.CompositionConstraints

namespace ResearchMain.Domination

open Classical

set_option maxHeartbeats 1000000

@[irreducible] noncomputable def boundedComposition {r N : ℕ} (bounds : Fin r → ℕ) (p : Fin r → ℕ)
    (hp : p ∈ (boundedParts bounds).filter (fun p => ∑ i, p i = N)) : Composition N :=
  compositionOfParts p (fun i => ((mem_boundedParts bounds p).mp
    (Finset.mem_filter.mp hp).1 i).1) (Finset.mem_filter.mp hp).2

@[simp] theorem boundedComposition_length {r N : ℕ} (bounds : Fin r → ℕ)
    (p : Fin r → ℕ) (hp : p ∈ (boundedParts bounds).filter (fun p => ∑ i, p i = N)) :
    (boundedComposition (N := N) bounds p hp).length = r := by
  unfold boundedComposition
  exact compositionOfParts_length p _ _

theorem boundedComposition_blocks {r N : ℕ} (bounds : Fin r → ℕ)
    (p : Fin r → ℕ) (hp : p ∈ (boundedParts bounds).filter (fun p => ∑ i, p i = N)) :
    (boundedComposition (N := N) bounds p hp).blocks = List.ofFn p := by
  unfold boundedComposition compositionOfParts
  rfl

theorem dominationCount_pathPower (n k ℓ : ℕ) :
    dominationCount (pathPower n ℓ) (k + 1) =
      compositionCount (pathBounds (k + 2) ℓ) (n + 1) := by
  classical
  symm
  unfold compositionCount dominationCount
  apply Finset.card_bij
    (fun p hp => selectedVertices (boundedComposition (pathBounds (k + 2) ℓ) p hp))
  · intro p hp
    let c := boundedComposition (pathBounds (k + 2) ℓ) p hp
    have hlen : c.length = k + 2 := boundedComposition_length _ _ _
    apply (mem_dominatingSets _ _ _).mpr
    constructor
    · change (selectedVertices c).card = k + 1
      have hc := selectedVertices_card c
      omega
    · apply (composition_path_bounds c hlen).mpr
      intro i
      let j := Fin.cast hlen i
      have hparts : fixedParts c hlen = p := fixedParts_eq_of_blocks c p hlen
        (boundedComposition_blocks _ _ _)
      have h := ((mem_boundedParts _ p).mp (Finset.mem_filter.mp hp).1 j).2
      rw [← hparts] at h
      change c.blocksFun (Fin.cast hlen.symm j) ≤ pathBounds (k + 2) ℓ j at h
      have hi : Fin.cast hlen.symm j = i := Fin.ext rfl
      rw [hi] at h
      simpa only [pathBounds, j, Fin.val_cast, hlen] using h
  · intro p hp q hq heq
    have hc : boundedComposition (pathBounds (k + 2) ℓ) p hp =
        boundedComposition (pathBounds (k + 2) ℓ) q hq :=
      (compositionSetEquiv n).injective heq
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
    have hbounds : ∀ i, c.blocksFun i ≤ pathBounds c.length ℓ i := by
      apply (composition_path_bounds c hlen).mp
      rw [hselected]
      exact hdom
    have hp : p ∈ (boundedParts (pathBounds (k + 2) ℓ)).filter
        (fun p => ∑ i, p i = n + 1) := by
      apply Finset.mem_filter.mpr
      constructor
      · apply (mem_boundedParts _ _).mpr
        intro i
        constructor
        · exact c.one_le_blocksFun (Fin.cast hlen.symm i)
        · have h := hbounds (Fin.cast hlen.symm i)
          change c.blocksFun (Fin.cast hlen.symm i) ≤ pathBounds (k + 2) ℓ i
          simpa only [pathBounds, Fin.val_cast, hlen] using h
      · exact fixedParts_sum c hlen
    refine ⟨p, hp, ?_⟩
    unfold boundedComposition
    change selectedVertices (compositionOfParts (fixedParts c hlen) _ _) = S
    rw [compositionOfParts_fixedParts]
    exact hselected

end ResearchMain.Domination
