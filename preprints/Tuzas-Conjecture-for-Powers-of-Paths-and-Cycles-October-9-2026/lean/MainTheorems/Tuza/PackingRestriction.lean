import MainTheorems.Tuza.CliquePacking

namespace ResearchMain.Tuza

variable {V : Type*} [DecidableEq V]

theorem clique_of_triangle_edges {G H : SimpleGraph V} {t : Finset V}
    (ht : H.IsNClique 3 t) (h : ∀ e ∈ triangleEdges t, e ∈ G.edgeSet) : G.IsNClique 3 t := by
  refine ⟨?_, ht.card_eq⟩
  intro x hx y hy hxy
  exact h s(x, y) (mem_triangleEdges.mpr ⟨hx, hy, hxy⟩)

theorem missing_triangle_edge {G H : SimpleGraph V} {t : Finset V}
    (ht : H.IsNClique 3 t) (hg : ¬ G.IsNClique 3 t) :
    ∃ e ∈ triangleEdges t, e ∉ G.edgeSet := by
  classical
  by_contra hn
  push Not at hn
  exact hg (clique_of_triangle_edges ht hn)

variable [Fintype V]

theorem restrict_packing {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {P : Finset (Finset V)} (hP : Packing H P) :
    ∃ Q : Finset (Finset V), Packing G Q ∧ Q ⊆ P ∧
      P.card ≤ Q.card + (H.edgeFinset \ G.edgeFinset).card := by
  classical
  let Q := P.filter (G.IsNClique 3)
  let B := P.filter (fun t => ¬ G.IsNClique 3 t)
  let E := H.edgeFinset \ G.edgeFinset
  have hQ : Packing G Q := by
    refine ⟨fun t ht => (Finset.mem_filter.mp ht).2, hP.2.mono ?_⟩
    exact_mod_cast Finset.filter_subset _ P
  have hbad : ∀ t : B, ∃ e : E, e.val ∈ triangleEdges t.val := by
    intro t
    have ht := Finset.mem_filter.mp t.property
    obtain ⟨e, he, hg⟩ := missing_triangle_edge (hP.1 t.val ht.1) ht.2
    have hhe : e ∈ H.edgeFinset := H.mem_edgeFinset.mpr (triangleEdges_subset (hP.1 t.val ht.1) e he)
    have hge : e ∉ G.edgeFinset := fun h => hg (G.mem_edgeFinset.mp h)
    exact ⟨⟨e, Finset.mem_sdiff.mpr ⟨hhe, hge⟩⟩, he⟩
  choose f hf using hbad
  have hfinj : Function.Injective f := by
    intro t u htu
    by_contra hne
    have hne' : t.val ≠ u.val := fun h => hne (Subtype.ext h)
    have hdis := hP.2 (Finset.mem_filter.mp t.property).1 (Finset.mem_filter.mp u.property).1 hne'
    apply Finset.disjoint_left.mp hdis (hf t)
    simpa only [htu] using hf u
  have hb : B.card ≤ E.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hfinj
  have hc : Q.card + B.card = P.card := Finset.card_filter_add_card_filter_not (s := P) _
  refine ⟨Q, hQ, Finset.filter_subset _ P, ?_⟩
  change P.card ≤ Q.card + E.card
  omega

end ResearchMain.Tuza
