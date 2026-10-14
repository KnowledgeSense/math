import EdgeColoringMixing.ObservedCopy
import EdgeColoringMixing.SideTransport
import EdgeColoringMixing.CutAgreement

set_option autoImplicit false

namespace EdgeColoringMixing.ObservedCounting
open SimpleGraph RootedCounting PinningForbidden ActualColorings
universe u v
variable {V : Type u} {O : Type v} {H : SimpleGraph V} {G : SimpleGraph O}

/-- An actual side inherits the free-subtree placement from an enclosing residual copy. -/
noncomputable def sideRootPlacement (Λ : Finset G.edgeSet) (C : SimpleGraph.Copy H G)
    (hfree : ∀ e : H.edgeSet, C.toLineGraphEmbedding e ∉ Λ)
    (x y r : V) (hxy : H.Adj x y) (hr : r ∈ s(x,y))
    (p : G.edgeSet) (hmap : C.toLineGraphEmbedding ⟨s(x,y),hxy⟩ = p) :
    RootPlacement (sideGraph (G := H) x y r) G Λ (sideRoot x y r) p where
  copy := C.comp (sideCopy x y r)
  free_edges e := by
    rw [copy_lineGraph_comp]
    exact hfree _
  incoming_free := hmap ▸ hfree ⟨s(x,y),hxy⟩
  root_incident := by
    have h : C r ∈ (C.toLineGraphEmbedding ⟨s(x,y),hxy⟩).1 :=
      Sym2.mem_map.mpr ⟨r, hr, rfl⟩
    rw [hmap] at h
    exact h
  incoming_ne e := by
    rw [copy_lineGraph_comp, ← hmap]
    intro he
    exact side_edge_ne x y r hxy e (C.toLineGraphEmbedding.injective he).symm

/-- Both sides of the observed residual-tree edge have the exact original incoming edge. -/
noncomputable def observedSidePlacement (G : SimpleGraph O) (Λ : Finset G.edgeSet)
    (e : FreeEdge G Λ) (x y r : observedComponent G Λ e)
    (hxy : (observedTree G Λ e).Adj x y)
    (he : (⟨s(x,y),hxy⟩ : (observedTree G Λ e).edgeSet) = observedEdge G Λ e)
    (hr : r ∈ s(x,y)) :
    RootPlacement (sideGraph (G := observedTree G Λ e) x y r) G Λ (sideRoot x y r) e.1 :=
  sideRootPlacement Λ (observedCopy G Λ e) (observedCopy_edge_free G Λ e)
    x y r hxy hr e.1 (by rw [he, observedCopy_observedEdge])

/-- Distance in the original pinned graph forces agreement throughout either actual side. -/
theorem observedSide_agreeToDepth [Fintype O] (G : SimpleGraph O) {q : ℕ}
    (Λ : Finset G.edgeSet) (τ τ' : Λ → Fin q) (e : FreeEdge G Λ)
    (x y r : observedComponent G Λ e) (hxy : (observedTree G Λ e).Adj x y)
    (he : (⟨s(x,y),hxy⟩ : (observedTree G Λ e).edgeSet) = observedEdge G Λ e)
    (hr : r ∈ s(x,y)) (n : ℕ)
    (hn : (n : ℕ∞) < disagreementDistance G Λ τ τ' e.1) :
    AgreeToDepth n (sideGraph (G := observedTree G Λ e) x y r) (sideRoot x y r) q
      (fun v => forbidden G q Λ τ v.1.1) (fun v => forbidden G q Λ τ' v.1.1) := by
  apply agreeToDepth_of_rootPlacement G Λ τ τ' e.1 n _ _
    (observedSidePlacement G Λ e x y r hxy he hr) _ _ _ hn
  intro v hv
  exact forbidden_eq_of_incident_agreement G q Λ τ τ' v.1.1 hv

end EdgeColoringMixing.ObservedCounting
