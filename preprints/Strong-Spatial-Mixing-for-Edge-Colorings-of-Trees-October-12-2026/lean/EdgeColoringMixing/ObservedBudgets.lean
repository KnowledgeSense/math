import EdgeColoringMixing.ObservedCopy
import EdgeColoringMixing.SideBudgets

set_option autoImplicit false

namespace EdgeColoringMixing.ObservedCounting
open SimpleGraph RootedCounting PinningForbidden ActualColorings
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V) (q : ℕ)
    (Λ : Finset G.edgeSet) (τ : Λ → Fin q)

/-- The original degree bound gives the exact budget on either observed residual side. -/
theorem observedSide_vertexBudget {Δ : ℕ} (hΔ : DegreeBound G Δ) (e : FreeEdge G Λ)
    (x y r : observedComponent G Λ e) :
    VertexBudget Δ q (sideGraph (G := observedTree G Λ e) x y r)
      (fun v => forbidden G q Λ τ v.1.1) :=
  side_vertexBudget (fun v => observed_vertex_budget G q Λ τ hΔ e v) x y r

/-- One additional unit is reserved for the actual observed edge removed at the side root. -/
theorem observedSide_rootBudget {Δ : ℕ} (hΔ : DegreeBound G Δ) (e : FreeEdge G Λ)
    (x y r z : observedComponent G Λ e) (he : s(r,z) = s(x,y))
    (hrz : (observedTree G Λ e).Adj r z) :
    RootBudget Δ q (sideGraph (G := observedTree G Λ e) x y r) (sideRoot x y r)
      (fun v => forbidden G q Λ τ v.1.1) :=
  side_rootBudget (fun v => observed_vertex_budget G q Λ τ hΔ e v) x y r z he hrz

end EdgeColoringMixing.ObservedCounting
