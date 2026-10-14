import MainTheorems.Laminar.MergeLabels

namespace ResearchMain.Laminar

open Classical

variable {R E U : Type*} [Fintype U] [LinearOrder U]

noncomputable def mergeCut (next : R → R) (parts : U → R → Finset E)
    (i : R) (u : U) (t : ℕ) : ℕ :=
  familyPrefix next (mergeLabels parts) (fun j => toLex (u, j)) (parts u i).card t i

theorem mergeCut_le (next : R → R) (parts : U → R → Finset E) (i : R) (u : U) (t : ℕ) :
    mergeCut next parts i u t ≤ (parts u i).card :=
  familyPrefix_le next (mergeLabels parts) _ _ t i

theorem mergeCut_iff (next : R → R) (parts : U → R → Finset E) (i : R) (u : U) (t : ℕ)
    (j : Fin (parts u i).card) :
    position next (mergeLabels parts) i (toLex (u, j.val)) < t ↔
      j.val < mergeCut next parts i u t := by
  apply familyPrefix_iff next (mergeLabels parts) _ (fun i => (parts u i).card)
  · exact fun i j => mem_mergeLabels parts i u j
  · intro a b hab
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hab⟩)

theorem mergeCut_transition (next : R → R) (parts : U → R → Finset E)
    (i : R) (u : U) (t : ℕ) :
    min (mergeCut next parts (next i) u t) (parts u i).card ≤ mergeCut next parts i u t := by
  apply familyPrefix_transition next (mergeLabels parts) _ (fun i => (parts u i).card)
  · exact fun i j => mem_mergeLabels parts i u j
  · intro a b hab
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hab⟩)

theorem mergeValue_child (parts : U → R → Finset E) (orders : ∀ u, Ordering (parts u))
    (i : R) (u : U) (j : Fin (parts u i).card) :
    (mergeValue parts orders i
      ⟨toLex (u, j.val), (mem_mergeLabels parts i u j.val).mpr j.isLt⟩).val =
      (orders u i j).val := rfl

theorem merged_prefix_child (next : R → R) (parts : U → R → Finset E)
    (orders : ∀ u, Ordering (parts u))
    (hdisj : ∀ i u v, u ≠ v → Disjoint (parts u i) (parts v i))
    (i : R) (u : U) (t : ℕ) :
    rowPrefix (mergedOrder next parts orders hdisj) i t ∩ parts u i =
      rowPrefix (orders u) i (mergeCut next parts i u t) := by
  ext e
  constructor
  · intro he
    obtain ⟨hep, heu⟩ := Finset.mem_inter.mp he
    let j := (orders u i).symm ⟨e, heu⟩
    let a : mergeLabels parts i :=
      ⟨toLex (u, j.val), (mem_mergeLabels parts i u j.val).mpr j.isLt⟩
    have hva : (mergeEquiv parts orders hdisj i a).val = e := by
      exact congrArg Subtype.val ((orders u i).apply_symm_apply ⟨e, heu⟩)
    have hp := (mem_prefix_iff_position (mergedOrder next parts orders hdisj) i t
      (mergeEquiv parts orders hdisj i a)).mp (hva.symm ▸ hep)
    rw [mergedOrder_position] at hp
    have hj := (mergeCut_iff next parts i u t j).mp hp
    exact (mem_prefix_iff_position (orders u) i _ ⟨e, heu⟩).mpr hj
  · intro he
    have heu := prefix_subset (orders u) i _ he
    let j := (orders u i).symm ⟨e, heu⟩
    let a : mergeLabels parts i :=
      ⟨toLex (u, j.val), (mem_mergeLabels parts i u j.val).mpr j.isLt⟩
    have hva : (mergeEquiv parts orders hdisj i a).val = e := by
      exact congrArg Subtype.val ((orders u i).apply_symm_apply ⟨e, heu⟩)
    have hj := (mem_prefix_iff_position (orders u) i _ ⟨e, heu⟩).mp he
    have hp := (mergeCut_iff next parts i u t j).mpr hj
    have hep := (mem_prefix_iff_position (mergedOrder next parts orders hdisj) i t
      (mergeEquiv parts orders hdisj i a)).mpr (by rw [mergedOrder_position]; exact hp)
    exact Finset.mem_inter.mpr ⟨hva ▸ hep, heu⟩

theorem merged_suffix_child (next : R → R) (parts : U → R → Finset E)
    (orders : ∀ u, Ordering (parts u))
    (hdisj : ∀ i u v, u ≠ v → Disjoint (parts u i) (parts v i))
    (i : R) (u : U) (t : ℕ) :
    rowSuffix (mergedOrder next parts orders hdisj) i t ∩ parts u i =
      rowSuffix (orders u) i (mergeCut next parts i u t) := by
  ext e
  by_cases heu : e ∈ parts u i
  · let j := (orders u i).symm ⟨e, heu⟩
    let a : mergeLabels parts i :=
      ⟨toLex (u, j.val), (mem_mergeLabels parts i u j.val).mpr j.isLt⟩
    have hva : (mergeEquiv parts orders hdisj i a).val = e := by
      exact congrArg Subtype.val ((orders u i).apply_symm_apply ⟨e, heu⟩)
    simp only [Finset.mem_inter, heu, and_true]
    rw [← hva, mem_suffix_iff_position, mergedOrder_position]
    rw [hva, mem_suffix_iff_position (orders u) i _ ⟨e, heu⟩]
    simpa only [not_lt] using not_congr (mergeCut_iff next parts i u t j)
  · have hen : e ∉ rowSuffix (orders u) i (mergeCut next parts i u t) :=
      fun h => heu (suffix_subset (orders u) i _ h)
    simp only [Finset.mem_inter, heu, and_false, hen]

theorem merged_child_window (next : R → R) (parts : U → R → Finset E)
    (orders : ∀ u, Ordering (parts u))
    (hdisj : ∀ i u v, u ≠ v → Disjoint (parts u i) (parts v i))
    (property : U → Finset E → Prop)
    (hmono : ∀ u X Y, X ⊆ Y → property u Y → property u X)
    (capacity : U → ℕ) (hsize : ∀ u i, (parts u i).card ≤ capacity u)
    (hrow : ∀ u i, property u (parts u i))
    (hwindow : ∀ u i t, t ≤ capacity u → property u (window (orders u) next i t))
    (i : R) (u : U) (t : ℕ) :
    property u ((rowSuffix (mergedOrder next parts orders hdisj) i t ∩ parts u i) ∪
      (rowPrefix (mergedOrder next parts orders hdisj) (next i) t ∩ parts u (next i))) := by
  rw [merged_suffix_child, merged_prefix_child]
  let a := mergeCut next parts i u t
  let b := mergeCut next parts (next i) u t
  have ha := mergeCut_le next parts i u t
  have hab := mergeCut_transition next parts i u t
  by_cases ham : a = (parts u i).card
  · rw [suffix_eq_empty (orders u) i (le_of_eq ham.symm), Finset.empty_union]
    exact hmono u _ _ (prefix_subset (orders u) (next i) b) (hrow u (next i))
  · have hba : b ≤ a := by omega
    apply hmono u _ (window (orders u) next i a)
    · exact Finset.union_subset_union (by rfl) (prefix_mono (orders u) (next i) hba)
    · exact hwindow u i a (ha.trans (hsize u i))

end ResearchMain.Laminar
