import EdgeColoringMixing.SideTransport
import EdgeColoringMixing.RootedInterpolation

set_option autoImplicit false

namespace EdgeColoringMixing.ObservedCounting
open Finset SimpleGraph RootedCounting
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Every inherited forbidden-color budget is valid on each actual side. -/
theorem side_vertexBudget [Fintype V] {Δ q : ℕ} {F : V → Finset (Fin q)}
    (h : VertexBudget Δ q G F) (x y r : V) :
    VertexBudget Δ q (sideGraph (G := G) x y r) (fun v => F v.1) := by
  intro v
  exact (Nat.add_le_add_left (side_neighbor_card_le x y r v) _).trans (h v.1)

/-- The deleted observed edge supplies the reserved unit at either side root. -/
theorem side_rootBudget [Fintype V] {Δ q : ℕ} {F : V → Finset (Fin q)}
    (h : VertexBudget Δ q G F) (x y r z : V)
    (he : s(r,z) = s(x,y)) (hrz : G.Adj r z) :
    RootBudget Δ q (sideGraph (G := G) x y r) (sideRoot x y r) (fun v => F v.1) := by
  have hdeg := side_root_degree_lt x y r z he hrz
  have hb := h r
  change (F r).card + Fintype.card ((sideGraph (G := G) x y r).neighborSet (sideRoot x y r)) + 1 ≤ Δ
  omega

end EdgeColoringMixing.ObservedCounting
