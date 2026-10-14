import MainTheorems.DominationRoots.SupportVertices

namespace ResearchMain.DominationRoots

open Classical ResearchMain.Domination

variable {V : Type} [Fintype V]

noncomputable def supportSet (G : SimpleGraph V) (R : Finset (Σ i, SupportFiber G i)) :
    Finset V := R.map (supportVertexEquiv G).toEmbedding

theorem mem_supportSet (G : SimpleGraph V) (R : Finset (Σ i, SupportFiber G i))
    (i : Option (CoreVertex G)) (w : SupportFiber G i) :
    supportVertex G ⟨i, w⟩ ∈ supportSet G R ↔ (⟨i, w⟩ : Σ i, SupportFiber G i) ∈ R := by
  change supportVertexEquiv G ⟨i, w⟩ ∈ R.map (supportVertexEquiv G).toEmbedding ↔ _
  simp

abbrev CoversSupport (G : SimpleGraph V) : ∀ i : Option (CoreVertex G), Finset (SupportFiber G i) → Prop
  | none, S => S = Finset.univ
  | some _, S => CoversStar S

theorem supportSet_dominates_iff (G : SimpleGraph V)
    (hne : ∀ v : CoreVertex G, (attachedLeaves G v.val).Nonempty)
    (R : Finset (Σ i, SupportFiber G i)) :
    Dominates G (supportSet G R) ↔ ∀ i, CoversSupport G i (subsetFiber R i) := by
  constructor
  · intro hdom i
    cases i with
    | none =>
      apply Finset.eq_univ_iff_forall.mpr
      intro v
      obtain ⟨u, hu, huv⟩ := hdom v.val
      have hm := (mem_closedNeighborhood G u v.val).mpr huv
      rw [(mem_isolatedVertices G v.val).mp v.property, Finset.mem_singleton] at hm
      subst u
      exact (mem_subsetFiber R none v).mpr ((mem_supportSet G R none v).mp hu)
    | some v =>
      change none ∈ subsetFiber R (some v) ∨ ∀ w, some w ∈ subsetFiber R (some v)
      by_cases hc : none ∈ subsetFiber R (some v)
      · exact Or.inl hc
      · right
        intro w
        obtain ⟨u, hu, huw⟩ := hdom w.val
        rcases huw with he | hadj
        · subst u
          exact (mem_subsetFiber R (some v) (some w)).mpr
            ((mem_supportSet G R (some v) (some w)).mp hu)
        · have he := selected_leaf_unique_neighbor (attached_selected w)
            hadj.symm (attached_adjacent w).symm
          subst u
          exact False.elim (hc ((mem_subsetFiber R (some v) none).mpr
            ((mem_supportSet G R (some v) none).mp hu)))
  · intro hlocal z
    obtain ⟨⟨i, w⟩, rfl⟩ := supportVertex_surjective G z
    cases i with
    | none =>
      have hm : w ∈ subsetFiber R none := by
        rw [show subsetFiber R none = Finset.univ from hlocal none]
        exact Finset.mem_univ _
      exact ⟨w.val, (mem_supportSet G R none w).mpr
        ((mem_subsetFiber R none w).mp hm), Or.inl rfl⟩
    | some v =>
      have hc : CoversStar (subsetFiber R (some v)) := hlocal (some v)
      rcases hc with hc | hl
      · have hm : v.val ∈ supportSet G R := (mem_supportSet G R (some v) none).mpr
          ((mem_subsetFiber R (some v) none).mp hc)
        cases w with
        | none => exact ⟨v.val, hm, Or.inl rfl⟩
        | some w => exact ⟨v.val, hm, Or.inr (attached_adjacent w)⟩
      · cases w with
        | none =>
          obtain ⟨u, hu⟩ := hne v
          let u' : ↥(attachedLeaves G v.val) := ⟨u, hu⟩
          have hm := (mem_supportSet G R (some v) (some u')).mpr
            ((mem_subsetFiber R (some v) (some u')).mp (hl u'))
          exact ⟨u, hm, Or.inr (attached_adjacent u').symm⟩
        | some w =>
          exact ⟨w.val, (mem_supportSet G R (some v) (some w)).mpr
            ((mem_subsetFiber R (some v) (some w)).mp (hl w)), Or.inl rfl⟩

end ResearchMain.DominationRoots
