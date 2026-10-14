import EdgeColoringMixing.TreeColorings

set_option autoImplicit false

/-! Separator facts for actual acyclic graphs, used in the edge-coloring recursion. -/
namespace EdgeColoringMixing.TreeGeometry
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Deleting a vertex separates all of its distinct neighbors in a forest. -/
theorem root_neighbors_separated (hG : G.IsAcyclic) (r : V)
    (x y : {v : V // v ≠ r}) (hx : G.Adj r x.1) (hy : G.Adj r y.1)
    (hconn : (G.induce {v | v ≠ r}).Reachable x y) : x = y := by
  classical
  obtain ⟨p, hp⟩ := hconn.exists_isPath
  let f : G.induce {v | v ≠ r} ↪g G := SimpleGraph.Embedding.induce _
  have hp' : (p.map f.toHom).IsPath := hp.map f.injective
  have hr : r ∉ (p.map f.toHom).support := by
    simp only [SimpleGraph.Walk.support_map, List.mem_map]
    rintro ⟨v, _, hvr⟩
    exact v.2 hvr
  have hpath : ((p.map f.toHom).cons hx).IsPath := hp'.cons hr
  have heq := hG.eq_snd_of_adj_start hpath hy
    (((p.map f.toHom).cons hx).end_mem_support)
  apply Subtype.ext
  exact (SimpleGraph.Walk.snd_cons (p.map f.toHom) hx).symm.trans heq.symm

/-- The neighbor-to-component map is injective for every finite tree, without
assuming a separately supplied branch decomposition. -/
theorem neighbor_component_injective (hG : G.IsAcyclic) (r : V) :
    Function.Injective (fun x : G.neighborSet r =>
      (G.induce {v | v ≠ r}).connectedComponentMk ⟨x.1, x.2.ne'⟩) := by
  intro x y h
  have hx := root_neighbors_separated hG r
    ⟨x.1, x.2.ne'⟩ ⟨y.1, y.2.ne'⟩ x.2 y.2
    (SimpleGraph.ConnectedComponent.exact h)
  exact Subtype.ext (congrArg (fun z : {v : V // v ≠ r} => z.1) hx)

/-- Every vertex outside the root is reachable, without returning to the root,
from one of its neighbors. -/
theorem exists_neighbor_reachable (hG : G.Connected) (r : V)
    (v : {v : V // v ≠ r}) :
    ∃ x : G.neighborSet r, (G.induce {v | v ≠ r}).Reachable
      ⟨x.1, x.2.ne'⟩ v := by
  classical
  obtain ⟨p, hp⟩ := hG.exists_isPath r v.1
  obtain ⟨x, hx, p, rfl⟩ := p.exists_eq_cons_of_ne v.2.symm
  have hr : r ∉ p.support := ((SimpleGraph.Walk.cons_isPath_iff hx p).mp hp).2
  refine ⟨⟨x, hx⟩, ?_⟩
  have hs : ∀ w ∈ p.support, w ∈ ({v : V | v ≠ r} : Set V) := by
    intro w hw hwr
    exact hr (hwr ▸ hw)
  exact ⟨p.induce {v | v ≠ r} hs⟩

/-- The components below an arbitrary root of a tree are exactly its child branches. -/
theorem neighbor_component_bijective (hG : G.IsTree) (r : V) :
    Function.Bijective (fun x : G.neighborSet r =>
      (G.induce {v | v ≠ r}).connectedComponentMk ⟨x.1, x.2.ne'⟩) := by
  refine ⟨neighbor_component_injective hG.isAcyclic r, ?_⟩
  intro K
  obtain ⟨v, hv⟩ := K.exists_rep
  obtain ⟨x, hx⟩ := exists_neighbor_reachable hG.connected r v
  refine ⟨x, ?_⟩
  exact (SimpleGraph.ConnectedComponent.sound hx).trans hv

/-- Canonical branch indexing by the actual neighbors of the root. -/
noncomputable def neighborComponentEquiv (hG : G.IsTree) (r : V) :
    G.neighborSet r ≃ (G.induce {v | v ≠ r}).ConnectedComponent :=
  Equiv.ofBijective _ (neighbor_component_bijective hG r)

/-- The unique branch containing a non-root vertex. -/
noncomputable def vertexBranch (hG : G.IsTree) (r : V) (v : {v : V // v ≠ r}) :
    G.neighborSet r := (neighborComponentEquiv hG r).symm
      ((G.induce {v | v ≠ r}).connectedComponentMk v)

@[simp] theorem vertexBranch_neighbor (hG : G.IsTree) (r : V) (x : G.neighborSet r) :
    vertexBranch hG r ⟨x.1, x.2.ne'⟩ = x :=
  (neighborComponentEquiv hG r).symm_apply_apply x

theorem vertexBranch_eq_of_adj (hG : G.IsTree) (r : V)
    (v w : {v : V // v ≠ r}) (hvw : G.Adj v.1 w.1) :
    vertexBranch hG r v = vertexBranch hG r w := by
  apply congrArg (neighborComponentEquiv hG r).symm
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hvw

/-- The root's incident edge leading to one of its actual children. -/
def rootEdge (r : V) (x : G.neighborSet r) : G.edgeSet := ⟨s(r, x.1), x.2⟩

@[simp] theorem root_mem_rootEdge (r : V) (x : G.neighborSet r) :
    r ∈ (rootEdge r x).1 := by simp [rootEdge]

@[simp] theorem child_mem_rootEdge (r : V) (x : G.neighborSet r) :
    x.1 ∈ (rootEdge r x).1 := by simp [rootEdge]

theorem rootEdge_injective (r : V) : Function.Injective (@rootEdge V G r) := by
  intro x y h
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  exact Sym2.congr_right.mp h'

/-- Internal edges are the original edges not incident to the root. -/
abbrev InternalEdge (G : SimpleGraph V) (r : V) := {e : G.edgeSet // r ∉ e.1}

noncomputable def edgeBranch (hG : G.IsTree) (r : V) (e : InternalEdge G r) :
    G.neighborSet r :=
  vertexBranch hG r ⟨e.1.1.out.1, fun h => e.2 ((congrArg (fun v : V => v ∈ e.1.1) h).mp
    (Sym2.out_fst_mem e.1.1))⟩

/-- Either endpoint of an internal edge yields the same branch. -/
theorem edgeBranch_eq_of_mem (hG : G.IsTree) (r : V) (e : InternalEdge G r)
    (v : {v : V // v ≠ r}) (hv : v.1 ∈ e.1.1) :
    edgeBranch hG r e = vertexBranch hG r v := by
  classical
  unfold edgeBranch
  by_cases heq : e.1.1.out.1 = v.1
  · exact congrArg (vertexBranch hG r) (Subtype.ext heq)
  · apply vertexBranch_eq_of_adj
    exact G.adj_iff_exists_edge.mpr
      ⟨heq, e.1.1, e.1.2, Sym2.out_fst_mem e.1.1, hv⟩

/-- Distinct branches have no internal adjacency. -/
theorem edgeBranch_eq_of_adj (hG : G.IsTree) (r : V) (e f : InternalEdge G r)
    (hef : G.lineGraph.Adj e.1 f.1) : edgeBranch hG r e = edgeBranch hG r f := by
  obtain ⟨_, v, he, hf⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hef
  let v' : {v : V // v ≠ r} := ⟨v, fun h => e.2 (h ▸ he)⟩
  exact (edgeBranch_eq_of_mem hG r e v' he).trans (edgeBranch_eq_of_mem hG r f v' hf).symm

/-- A root edge touches an internal edge precisely at its child endpoint. -/
theorem rootEdge_internal_adj_iff (r : V) (x : G.neighborSet r)
    (e : InternalEdge G r) : G.lineGraph.Adj (rootEdge r x) e.1 ↔ x.1 ∈ e.1.1 := by
  classical
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨_, v, hv, he⟩
    rcases Sym2.mem_iff.mp hv with h | h
    · exact False.elim (e.2 (h ▸ he))
    · exact h ▸ he
  · intro hx
    refine ⟨?_, x.1, child_mem_rootEdge r x, hx⟩
    intro heq
    exact e.2 (heq ▸ root_mem_rootEdge r x)

/-- A root edge interacts only with the corresponding internal branch. -/
theorem edgeBranch_eq_of_rootEdge_adj (hG : G.IsTree) (r : V)
    (x : G.neighborSet r) (e : InternalEdge G r)
    (h : G.lineGraph.Adj (rootEdge r x) e.1) : edgeBranch hG r e = x := by
  exact (edgeBranch_eq_of_mem hG r e ⟨x.1, x.2.ne'⟩
    ((rootEdge_internal_adj_iff r x e).mp h)).trans (vertexBranch_neighbor hG r x)

end EdgeColoringMixing.TreeGeometry
