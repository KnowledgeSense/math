import MainTheorems.DominationRoots.LeafSupports
import MainTheorems.DominationRoots.LocalStars

namespace ResearchMain.DominationRoots

open Classical

variable {V : Type} [Fintype V]

abbrev CoreVertex (G : SimpleGraph V) := ↥(coreVertices G)

abbrev LeafFiber {C : Type} (I : Type) (W : C → Type) : Option C → Type
  | none => I
  | some c => Option (W c)

noncomputable instance {C I : Type} {W : C → Type}
    [Fintype I] [∀ c, Fintype (W c)] (i : Option C) : Fintype (LeafFiber I W i) :=
  match i with
  | none => inferInstanceAs (Fintype I)
  | some c => inferInstanceAs (Fintype (Option (W c)))

abbrev SupportFiber (G : SimpleGraph V) :=
  LeafFiber ↥(isolatedVertices G) (fun v : CoreVertex G => ↥(attachedLeaves G v.val))

def supportVertex (G : SimpleGraph V) : (Σ i, SupportFiber G i) → V
  | ⟨none, v⟩ => v.val
  | ⟨some v, none⟩ => v.val
  | ⟨some _, some w⟩ => w.val

theorem core_not_selected {G : SimpleGraph V} (v : CoreVertex G) :
    v.val ∉ selectedLeaves G := by
  exact fun h => (Finset.mem_sdiff.mp v.property).2 (Finset.mem_union_left _ h)

theorem core_not_isolated {G : SimpleGraph V} (v : CoreVertex G) :
    v.val ∉ isolatedVertices G := by
  exact fun h => (Finset.mem_sdiff.mp v.property).2 (Finset.mem_union_right _ h)

theorem attached_selected {G : SimpleGraph V} {v : V} (w : ↥(attachedLeaves G v)) :
    w.val ∈ selectedLeaves G := (Finset.mem_filter.mp w.property).1

theorem attached_adjacent {G : SimpleGraph V} {v : V} (w : ↥(attachedLeaves G v)) :
    G.Adj v w.val := (Finset.mem_filter.mp w.property).2

theorem selected_not_isolated {G : SimpleGraph V} {v : V} (hv : v ∈ selectedLeaves G) :
    v ∉ isolatedVertices G := by
  intro hi
  have hcard := selectedLeaf_card hv
  rw [(mem_isolatedVertices G v).mp hi, Finset.card_singleton] at hcard
  omega

theorem supportVertex_injective (G : SimpleGraph V) : Function.Injective (supportVertex G) := by
  rintro ⟨_ | v, x⟩ ⟨_ | w, y⟩ h
  · dsimp [supportVertex] at h
    have he : x = y := Subtype.ext h
    subst y
    rfl
  · cases y with
    | none =>
      have he : x.val = w.val := h
      exact False.elim (core_not_isolated w (he ▸ x.property))
    | some y =>
      have he : x.val = y.val := h
      exact False.elim (selected_not_isolated (attached_selected y) (he ▸ x.property))
  · cases x with
    | none =>
      have he : v.val = y.val := h
      exact False.elim (core_not_isolated v (he.symm ▸ y.property))
    | some x =>
      have he : x.val = y.val := h
      exact False.elim (selected_not_isolated (attached_selected x) (he.symm ▸ y.property))
  · cases x with
    | none =>
      cases y with
      | none =>
        have he : v = w := Subtype.ext h
        subst w
        rfl
      | some y =>
        have he : v.val = y.val := h
        exact False.elim (core_not_selected v (he.symm ▸ attached_selected y))
    | some x =>
      cases y with
      | none =>
        have he : x.val = w.val := h
        exact False.elim (core_not_selected w (he ▸ attached_selected x))
      | some y =>
        have he : x.val = y.val := h
        have hp : v.val = w.val := selected_leaf_unique_neighbor (attached_selected x)
          (attached_adjacent x).symm (he.symm ▸ (attached_adjacent y).symm)
        have hp' : v = w := Subtype.ext hp
        subst w
        have hx : x = y := Subtype.ext he
        subst y
        rfl

theorem supportVertex_surjective (G : SimpleGraph V) : Function.Surjective (supportVertex G) := by
  intro v
  by_cases hi : v ∈ isolatedVertices G
  · exact ⟨⟨none, ⟨v, hi⟩⟩, rfl⟩
  · by_cases hs : v ∈ selectedLeaves G
    · obtain ⟨w, hw⟩ := leaf_neighbor_exists (selectedLeaf_card hs)
      have hc := selected_leaf_neighbor_core hs hw
      have hl : v ∈ attachedLeaves G w := Finset.mem_filter.mpr ⟨hs, hw.symm⟩
      exact ⟨⟨some ⟨w, hc⟩, some ⟨v, hl⟩⟩, rfl⟩
    · have hc : v ∈ coreVertices G := by simp [coreVertices, hs, hi]
      exact ⟨⟨some ⟨v, hc⟩, none⟩, rfl⟩

noncomputable def supportVertexEquiv (G : SimpleGraph V) : (Σ i, SupportFiber G i) ≃ V :=
  Equiv.ofBijective (supportVertex G) ⟨supportVertex_injective G, supportVertex_surjective G⟩

end ResearchMain.DominationRoots
