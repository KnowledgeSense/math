import MainTheorems.PreorderGamma.Macaulay.DirectedMatchings

namespace ResearchMain.PreorderGamma.Macaulay

variable {E : Type*} [DecidableEq E] [Preorder E]

omit [Preorder E] in
theorem leftSupport_union (M N : Finset (E × E)) :
    leftSupport (M ∪ N) = leftSupport M ∪ leftSupport N := Finset.image_union M N

omit [Preorder E] in
theorem rightSupport_union (M N : Finset (E × E)) :
    rightSupport (M ∪ N) = rightSupport M ∪ rightSupport N := Finset.image_union M N

theorem IsOrderMatching.leftSupport_sdiff {M N : Finset (E × E)}
    (hM : IsOrderMatching M) (hNM : N ⊆ M) :
    leftSupport (M \ N) = leftSupport M \ leftSupport N :=
  Finset.image_sdiff_of_injOn hM.left_injective hNM

theorem IsOrderMatching.rightSupport_sdiff {M N : Finset (E × E)}
    (hM : IsOrderMatching M) (hNM : N ⊆ M) :
    rightSupport (M \ N) = rightSupport M \ rightSupport N :=
  Finset.image_sdiff_of_injOn hM.right_injective hNM

omit [Preorder E] in
theorem disjoint_of_leftSupport {M N : Finset (E × E)}
    (h : Disjoint (leftSupport M) (leftSupport N)) : Disjoint M N := by
  apply Finset.disjoint_left.mpr
  intro e he hn
  exact Finset.disjoint_left.mp h
    (Finset.mem_image.mpr ⟨e, he, rfl⟩) (Finset.mem_image.mpr ⟨e, hn, rfl⟩)

theorem IsOrderMatching.union {M N : Finset (E × E)}
    (hM : IsOrderMatching M) (hN : IsOrderMatching N)
    (hl : Disjoint (leftSupport M) (leftSupport N))
    (hr : Disjoint (rightSupport M) (rightSupport N))
    (hc : Disjoint (leftSupport M ∪ leftSupport N) (rightSupport M ∪ rightSupport N)) :
    IsOrderMatching (M ∪ N) where
  ordered e he := (Finset.mem_union.mp he).elim (hM.ordered e) (hN.ordered e)
  left_injective := by
    intro e he d hd hed
    rcases Finset.mem_union.mp he with he | he <;>
      rcases Finset.mem_union.mp hd with hd | hd
    · exact hM.left_injective he hd hed
    · exact False.elim (Finset.disjoint_left.mp hl
        (Finset.mem_image.mpr ⟨e, he, rfl⟩)
        (hed.symm ▸ Finset.mem_image.mpr ⟨d, hd, rfl⟩))
    · exact False.elim (Finset.disjoint_left.mp hl
        (hed.symm ▸ Finset.mem_image.mpr ⟨d, hd, rfl⟩)
        (Finset.mem_image.mpr ⟨e, he, rfl⟩))
    · exact hN.left_injective he hd hed
  right_injective := by
    intro e he d hd hed
    rcases Finset.mem_union.mp he with he | he <;>
      rcases Finset.mem_union.mp hd with hd | hd
    · exact hM.right_injective he hd hed
    · exact False.elim (Finset.disjoint_left.mp hr
        (Finset.mem_image.mpr ⟨e, he, rfl⟩)
        (hed.symm ▸ Finset.mem_image.mpr ⟨d, hd, rfl⟩))
    · exact False.elim (Finset.disjoint_left.mp hr
        (hed.symm ▸ Finset.mem_image.mpr ⟨d, hd, rfl⟩)
        (Finset.mem_image.mpr ⟨e, he, rfl⟩))
    · exact hN.right_injective he hd hed
  disjoint := by
    rw [leftSupport_union, rightSupport_union]
    exact hc

theorem replacement_supports {M N T : Finset (E × E)}
    (hM : IsOrderMatching M) (hNM : N ⊆ M)
    (hl : leftSupport T = leftSupport N) (hr : rightSupport T = rightSupport N) :
    leftSupport (T ∪ (M \ N)) = leftSupport M ∧
      rightSupport (T ∪ (M \ N)) = rightSupport M := by
  constructor
  · rw [leftSupport_union, hl, hM.leftSupport_sdiff hNM,
      Finset.union_sdiff_of_subset (leftSupport_mono hNM)]
  · rw [rightSupport_union, hr, hM.rightSupport_sdiff hNM,
      Finset.union_sdiff_of_subset (rightSupport_mono hNM)]

theorem IsOrderMatching.replace {M N T : Finset (E × E)}
    (hM : IsOrderMatching M) (hNM : N ⊆ M) (hT : IsOrderMatching T)
    (hl : leftSupport T = leftSupport N) (hr : rightSupport T = rightSupport N) :
    IsOrderMatching (T ∪ (M \ N)) := by
  apply hT.union (hM.subset Finset.sdiff_subset)
  · rw [hl, hM.leftSupport_sdiff hNM]
    exact disjoint_sdiff_self_right
  · rw [hr, hM.rightSupport_sdiff hNM]
    exact disjoint_sdiff_self_right
  · have hs := replacement_supports hM hNM hl hr
    rw [← leftSupport_union, ← rightSupport_union, hs.1, hs.2]
    exact hM.disjoint

end ResearchMain.PreorderGamma.Macaulay
