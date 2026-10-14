import EdgeColoringMixing.PinningForbidden

set_option autoImplicit false

namespace EdgeColoringMixing.PinningForbidden
open ActualColorings ComponentRestriction SimpleGraph
universe u
variable {V : Type u} (G : SimpleGraph V) (Λ : Finset G.edgeSet)

/-- Literal inclusion of the actual observed residual component into the original graph. -/
noncomputable def observedCopy (e : FreeEdge G Λ) : SimpleGraph.Copy (observedTree G Λ e) G where
  toHom :=
    { toFun := Subtype.val
      map_rel' := fun h => (deleteEdges_adj.mp h).1 }
  injective' := Subtype.coe_injective

@[simp] theorem observedCopy_apply (e : FreeEdge G Λ) (v : observedComponent G Λ e) :
    observedCopy G Λ e v = v.1 := rfl

/-- Every edge in the observed component was genuinely left unpinned. -/
theorem observedCopy_edge_free (e : FreeEdge G Λ) (f : (observedTree G Λ e).edgeSet) :
    (observedCopy G Λ e).toLineGraphEmbedding f ∉ Λ := by
  rcases f with ⟨f, hf⟩
  induction f using Sym2.ind with
  | h v w =>
    intro hpin
    exact (deleteEdges_adj.mp hf).2 ⟨⟨_, hpin⟩, rfl⟩

/-- The canonical observed edge is exactly the original edge under inclusion. -/
@[simp] theorem observedCopy_observedEdge (e : FreeEdge G Λ) :
    (observedCopy G Λ e).toLineGraphEmbedding (observedEdge G Λ e) = e.1 := by
  apply Subtype.ext
  exact congrArg (fun f : (residualGraph G Λ).edgeSet => f.1) (componentEdgeEquiv_edgeInComponent
    (residualGraph G Λ) (residualEdgeEquiv G Λ e))

end EdgeColoringMixing.PinningForbidden
