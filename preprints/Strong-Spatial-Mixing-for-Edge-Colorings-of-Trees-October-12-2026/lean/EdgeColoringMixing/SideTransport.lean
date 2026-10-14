import EdgeColoringMixing.CutSides

set_option autoImplicit false

namespace EdgeColoringMixing.ObservedCounting
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} {G : SimpleGraph V}

noncomputable instance [Fintype V] (x y r : V) : Fintype (side (G := G) x y r) :=
  Fintype.ofFinite _

/-- Each side is an actual subgraph of the original graph by literal vertex inclusion. -/
def sideCopy (x y r : V) : SimpleGraph.Copy (sideGraph (G := G) x y r) G where
  toHom :=
    { toFun := Subtype.val
      map_rel' := fun h => (deleteEdges_adj.mp h).1 }
  injective' := Subtype.coe_injective

@[simp] theorem sideCopy_apply (x y r : V) (v : side (G := G) x y r) :
    sideCopy x y r v = v.1 := rfl

@[simp] theorem sideCopy_root (x y r : V) :
    sideCopy (G := G) x y r (sideRoot x y r) = r := rfl

/-- Side neighbors inject into the genuine original neighbors. -/
def sideNeighborEmbedding (x y r : V) (v : side (G := G) x y r) :
    (sideGraph (G := G) x y r).neighborSet v ↪ G.neighborSet v.1 :=
  (sideCopy x y r).mapNeighborSet v

theorem side_neighbor_card_le [Fintype V] (x y r : V) (v : side (G := G) x y r) :
    Fintype.card ((sideGraph (G := G) x y r).neighborSet v) ≤
      Fintype.card (G.neighborSet v.1) :=
  Fintype.card_le_of_injective _ (sideNeighborEmbedding x y r v).injective

/-- A neighbor across the deleted edge is absent at the side root. -/
def sideRootNeighborEmbedding (x y r z : V) (he : s(r,z) = s(x,y)) :
    (sideGraph (G := G) x y r).neighborSet (sideRoot x y r) ↪
      {w : G.neighborSet r // w.1 ≠ z} where
  toFun w := ⟨sideNeighborEmbedding x y r (sideRoot x y r) w, by
    intro hw
    change w.1.1 = z at hw
    have hnot := (deleteEdges_adj.mp w.2).2
    apply hnot
    change s(r, w.1.1) ∈ ({s(x,y)} : Set (Sym2 V))
    simp only [hw, he, Set.mem_singleton_iff]⟩
  inj' _ _ h := (sideNeighborEmbedding x y r (sideRoot x y r)).injective
    (congrArg Subtype.val h)

theorem side_root_degree_lt [Fintype V] (x y r z : V)
    (he : s(r,z) = s(x,y)) (hrz : G.Adj r z) :
    Fintype.card ((sideGraph (G := G) x y r).neighborSet (sideRoot x y r)) <
      Fintype.card (G.neighborSet r) := by
  apply (Fintype.card_le_of_injective _ (sideRootNeighborEmbedding x y r z he).injective).trans_lt
  exact Fintype.card_subtype_lt (x := (⟨z, hrz⟩ : G.neighborSet r)) (by simp)

/-- No actual side edge is the edge that was cut. -/
theorem side_edge_val_ne (x y r : V) (e : (sideGraph (G := G) x y r).edgeSet) :
    ((sideCopy x y r).toLineGraphEmbedding e).1 ≠ s(x,y) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h v w =>
    change s(v.1,w.1) ≠ s(x,y)
    exact fun h => (deleteEdges_adj.mp he).2 (Set.mem_singleton_iff.mpr h)

theorem side_edge_ne (x y r : V) (hxy : G.Adj x y)
    (e : (sideGraph (G := G) x y r).edgeSet) :
    (sideCopy x y r).toLineGraphEmbedding e ≠ (⟨s(x,y), hxy⟩ : G.edgeSet) := by
  intro h
  exact side_edge_val_ne x y r e (congrArg Subtype.val h)

/-- The opposite endpoint is absent from a genuine tree side. -/
theorem side_vertex_ne_opposite (hG : G.IsTree) (x y r z : V)
    (he : s(r,z) = s(x,y)) (hrz : G.Adj r z) (v : side (G := G) x y r) :
    v.1 ≠ z := by
  intro hv
  have hreach := (SimpleGraph.ConnectedComponent.exact v.2).symm
  change (cutGraph (G := G) x y).Reachable r v.1 at hreach
  rw [hv] at hreach
  have hcut : cutGraph (G := G) x y = cutGraph (G := G) r z := by
    unfold cutGraph
    rw [he]
  rw [hcut] at hreach
  exact cut_not_reachable hG hrz hreach

/-- Cutting a genuine tree edge gives strictly smaller vertex sets on both sides. -/
theorem side_card_lt [Fintype V] (hG : G.IsTree) (x y r z : V)
    (he : s(r,z) = s(x,y)) (hrz : G.Adj r z) :
    Fintype.card (side (G := G) x y r) < Fintype.card V := by
  let f : side (G := G) x y r → {v : V // v ≠ z} :=
    fun v => ⟨v.1, side_vertex_ne_opposite hG x y r z he hrz v⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun w : {v : V // v ≠ z} => w.1) hab)
  exact (Fintype.card_le_of_injective f hf).trans_lt
    (Fintype.card_subtype_lt (x := z) (by simp))

end EdgeColoringMixing.ObservedCounting
