import MainTheorems.Tuza.FanPacking
import MainTheorems.Tuza.VertexStars

namespace ResearchMain.Tuza

variable {V : Type*} [DecidableEq V]

theorem exists_restricted_packing {G : SimpleGraph V} {P : Finset (Finset V)} (hP : Packing G P)
    (p : V → Prop) (hp : ∀ t ∈ P, ∀ x ∈ t, p x) :
    ∃ Q : Finset (Finset {x : V // p x}), Packing (G.induce {x | p x}) Q ∧ Q.card = P.card := by
  classical
  let T : P → Finset {x : V // p x} := fun t => t.val.subtype p
  have hT (t : P) : (T t).map (Function.Embedding.subtype p) = t.val :=
    Finset.subtype_map_of_mem (hp t.val t.property)
  let F : PackingFamily (G.induce {x | p x}) P := {
    triangle := T
    clique := fun t => by
      apply (G.isNClique_induce_iff {x | p x} (T t) 3).mpr
      change G.IsNClique 3 ((T t).map (Function.Embedding.subtype p))
      rw [hT]
      exact hP.1 t.val t.property
    disjoint := fun t u htu => by
      apply (Finset.disjoint_map (Function.Embedding.subtype p).sym2Map).mp
      rw [← triangleEdges_map, ← triangleEdges_map, hT, hT]
      exact hP.2 t.property u.property (fun he => htu (Subtype.ext he)) }
  exact ⟨F.carrier, F.packing, F.card.trans (Fintype.card_coe P)⟩

theorem exists_vertex_deleted_packing [Fintype V] (D : TriangleDecomposition (⊤ : SimpleGraph V))
    (v : V) : ∃ P : Finset (Finset {x : V // x ≠ v}),
      Packing (⊤ : SimpleGraph {x : V // x ≠ v}) P ∧
        3 * P.card + 3 * ((Fintype.card V - 1) / 2) = (Fintype.card V).choose 2 := by
  classical
  let R := D.triangles.filter (fun t => v ∉ t)
  have hR : Packing (⊤ : SimpleGraph V) R := D.packing.subset (Finset.filter_subset _ _)
  have hp : ∀ t ∈ R, ∀ x ∈ t, x ≠ v := by
    intro t ht x hx hxeq
    exact (Finset.mem_filter.mp ht).2 (hxeq ▸ hx)
  obtain ⟨P, hP, hcard⟩ := exists_restricted_packing hR (fun x => x ≠ v) hp
  have ht : (⊤ : SimpleGraph V).induce {x | x ≠ v} = (⊤ : SimpleGraph {x : V // x ≠ v}) := by
    ext x y
    simp
  rw [ht] at hP
  have hc := D.vertex_count v
  have hd : (⊤ : SimpleGraph V).degree v = Fintype.card V - 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_top,
      Finset.card_compl, Finset.card_singleton]
  rw [hd] at hc
  have hhalf : (D.triangles.filter (v ∈ ·)).card = (Fintype.card V - 1) / 2 := by omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := D.triangles) (fun t => v ∈ t)
  refine ⟨P, hP, ?_⟩
  rw [hcard, ← hhalf]
  have hcount := D.card
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two] at hcount
  dsimp only [R]
  omega

theorem exists_vertex_removed_packing [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (D : TriangleDecomposition G) (v : V) :
    ∃ P : Finset (Finset {x : V // x ≠ v}), Packing (G.induce {x | x ≠ v}) P ∧
      3 * P.card + 3 * (G.degree v / 2) = G.edgeFinset.card := by
  classical
  let R := D.triangles.filter (fun t => v ∉ t)
  have hR : Packing G R := D.packing.subset (Finset.filter_subset _ _)
  have hp : ∀ t ∈ R, ∀ x ∈ t, x ≠ v := by
    intro t ht x hx hxeq
    exact (Finset.mem_filter.mp ht).2 (hxeq ▸ hx)
  obtain ⟨P, hP, hcard⟩ := exists_restricted_packing hR (fun x => x ≠ v) hp
  have hc := D.vertex_count v
  have hhalf : (D.triangles.filter (v ∈ ·)).card = G.degree v / 2 := by omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := D.triangles) (fun t => v ∈ t)
  refine ⟨P, hP, ?_⟩
  rw [hcard, ← hhalf]
  have hcount := D.card
  dsimp only [R]
  omega

end ResearchMain.Tuza
