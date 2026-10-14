import EdgeColoringMixing.ChildTree

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EdgeColoringMixing.ObservedCounting
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- The genuine graph obtained by deleting the observed edge. -/
def cutGraph (x y : V) : SimpleGraph V := G.deleteEdges {s(x,y)}

/-- Every vertex of a connected graph lies on one of the two endpoint sides. -/
theorem cut_reachable_or (hG : G.Connected) (x y v : V) :
    (cutGraph (G := G) x y).Reachable x v ∨
      (cutGraph (G := G) x y).Reachable y v := by
  obtain ⟨p⟩ := hG v x
  have step : ∀ {a b : V}, G.Adj a b →
      ((cutGraph (G := G) x y).Reachable x b ∨
        (cutGraph (G := G) x y).Reachable y b) →
      ((cutGraph (G := G) x y).Reachable x a ∨
        (cutGraph (G := G) x y).Reachable y a) := by
    intro a b hab hb
    by_cases he : s(a,b) = s(x,y)
    · have ha : a = x ∨ a = y := by
        have hm : a ∈ s(x,y) := he ▸ (by simp : a ∈ s(a,b))
        simpa using hm
      rcases ha with rfl | rfl
      · exact Or.inl (.refl _)
      · exact Or.inr (.refl _)
    · have hd : (cutGraph (G := G) x y).Adj a b :=
        deleteEdges_adj.mpr ⟨hab, by simpa using he⟩
      exact hb.imp (fun h => h.trans hd.symm.reachable) (fun h => h.trans hd.symm.reachable)
  induction p with
  | nil => exact Or.inl (.refl _)
  | cons h p ih => exact step h (ih step)

/-- In a tree the two endpoint sides are disjoint. -/
theorem cut_not_reachable (hG : G.IsTree) {x y : V} (hxy : G.Adj x y) :
    ¬ (cutGraph (G := G) x y).Reachable x y :=
  isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hG.isAcyclic hxy)

/-- The exact connected component rooted at an endpoint of the cut. -/
def side (x y r : V) : (cutGraph (G := G) x y).ConnectedComponent :=
  (cutGraph (G := G) x y).connectedComponentMk r

def sideGraph (x y r : V) : SimpleGraph (side (G := G) x y r) :=
  (side (G := G) x y r).toSimpleGraph

def sideRoot (x y r : V) : side (G := G) x y r := ⟨r,rfl⟩

theorem sideGraph_isTree (hG : G.IsTree) (x y r : V) :
    (sideGraph (G := G) x y r).IsTree :=
  (SimpleGraph.IsAcyclic.anti (deleteEdges_le _) hG.isAcyclic).isTree_connectedComponent _

end EdgeColoringMixing.ObservedCounting
