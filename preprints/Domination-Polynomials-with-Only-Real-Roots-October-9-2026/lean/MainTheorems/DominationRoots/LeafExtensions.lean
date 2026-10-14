import MainTheorems.DominationRoots.Classification
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace ResearchMain.DominationRoots

open Classical

variable {C I : Type} {W : C → Type}

def leafExtensionAdj (H : SimpleGraph C) :
    (Σ i, LeafFiber I W i) → (Σ i, LeafFiber I W i) → Prop
  | ⟨some c, none⟩, ⟨some d, none⟩ => H.Adj c d
  | ⟨some c, none⟩, ⟨some d, some _⟩ => c = d
  | ⟨some c, some _⟩, ⟨some d, none⟩ => c = d
  | _, _ => False

def leafExtension (H : SimpleGraph C) (I : Type) (W : C → Type) :
    SimpleGraph (Σ i, LeafFiber I W i) where
  Adj := leafExtensionAdj H
  symm.symm := by
    rintro ⟨_ | c, x⟩ ⟨_ | d, y⟩ h
    · exact h
    · cases y <;> exact False.elim h
    · cases x <;> exact False.elim h
    · cases x <;> cases y
      · exact h.symm
      · exact h.symm
      · exact h.symm
      · exact h
  loopless.irrefl := by
    rintro ⟨_ | c, x⟩
    · exact id
    · cases x
      · exact H.irrefl
      · exact id

variable {V : Type} [Fintype V]

noncomputable def coreGraph (G : SimpleGraph V) : SimpleGraph (CoreVertex G) :=
  G.comap Subtype.val

theorem supportVertex_adj_iff (G : SimpleGraph V) (p q : Σ i, SupportFiber G i) :
    G.Adj (supportVertex G p) (supportVertex G q) ↔
      (leafExtension (coreGraph G) ↥(isolatedVertices G)
        (fun v : CoreVertex G => ↥(attachedLeaves G v.val))).Adj p q := by
  rcases p with ⟨_ | v, x⟩ <;> rcases q with ⟨_ | w, y⟩
  · change G.Adj x.val y.val ↔ False
    constructor
    · intro h
      have hm := (mem_closedNeighborhood G y.val x.val).mpr (Or.inr h.symm)
      rw [(mem_isolatedVertices G x.val).mp x.property, Finset.mem_singleton] at hm
      exact h.ne hm.symm
    · exact False.elim
  · change G.Adj x.val (supportVertex G ⟨some w, y⟩) ↔ False
    constructor
    · intro h
      have hm := (mem_closedNeighborhood G _ x.val).mpr (Or.inr h.symm)
      rw [(mem_isolatedVertices G x.val).mp x.property, Finset.mem_singleton] at hm
      exact h.ne hm.symm
    · exact False.elim
  · have hi (u : V) : ¬G.Adj u y.val := by
      intro h
      have hm := (mem_closedNeighborhood G u y.val).mpr (Or.inr h)
      rw [(mem_isolatedVertices G y.val).mp y.property, Finset.mem_singleton] at hm
      exact h.ne hm
    cases x <;> exact iff_false_intro (hi _)
  · cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        change G.Adj v.val y.val ↔ v = w
        constructor
        · intro h
          exact Subtype.ext (selected_leaf_unique_neighbor (attached_selected y)
            h.symm (attached_adjacent y).symm)
        · rintro rfl
          exact attached_adjacent y
    | some x =>
      cases y with
      | none =>
        change G.Adj x.val w.val ↔ v = w
        constructor
        · intro h
          exact Subtype.ext (selected_leaf_unique_neighbor (attached_selected x)
            (attached_adjacent x).symm h)
        · rintro rfl
          exact (attached_adjacent x).symm
      | some y =>
        change G.Adj x.val y.val ↔ False
        exact iff_false_intro (selectedLeaves_not_adjacent (attached_selected x) (attached_selected y))

noncomputable def supportGraphIso (G : SimpleGraph V) :
    leafExtension (coreGraph G) ↥(isolatedVertices G)
      (fun v : CoreVertex G => ↥(attachedLeaves G v.val)) ≃g G where
  toEquiv := supportVertexEquiv G
  map_rel_iff' := supportVertex_adj_iff G _ _

end ResearchMain.DominationRoots
