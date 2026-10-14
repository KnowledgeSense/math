import MainTheorems.Tuza.PackingEdges

namespace ResearchMain.Tuza

variable {V : Type*} [DecidableEq V]

theorem vertex_mem_of_triangleEdge {t : Finset V} {e : Sym2 V} {v : V}
    (he : e ∈ triangleEdges t) (hv : v ∈ e) : v ∈ t := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    obtain ⟨ha, hb, _⟩ := mem_triangleEdges.mp he
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ha
    · exact hb

def vertexStar (t : Finset V) (v : V) : Finset (Sym2 V) := (triangleEdges t).filter (v ∈ ·)

theorem vertexStar_card {G : SimpleGraph V} {t : Finset V} (ht : G.IsNClique 3 t)
    {v : V} (hv : v ∈ t) : (vertexStar t v).card = 2 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := G.is3Clique_iff.mp ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  all_goals
    rw [vertexStar, triangleEdges_triple hab.ne hac.ne hbc.ne]
    simp only [Finset.filter_insert, Finset.filter_singleton, Sym2.mem_iff]
    simp [hab.ne, hac.ne, hbc.ne, hab.ne.symm, hac.ne.symm, hbc.ne.symm]

variable [Fintype V]

theorem TriangleDecomposition.vertex_stars {G : SimpleGraph V} [DecidableRel G.Adj]
    (D : TriangleDecomposition G) (v : V) :
    (D.triangles.filter (v ∈ ·)).biUnion (fun t => vertexStar t v) = G.incidenceFinset v := by
  ext e
  constructor
  · intro he
    obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.mp he
    obtain ⟨he', hv⟩ := Finset.mem_filter.mp het
    have heG := triangleEdges_subset (D.packing.1 t (Finset.mem_filter.mp ht).1) e he'
    rw [G.incidenceFinset_eq_filter]
    exact Finset.mem_filter.mpr ⟨G.mem_edgeFinset.mpr heG, hv⟩
  · intro he
    rw [G.incidenceFinset_eq_filter] at he
    obtain ⟨heG, hv⟩ := Finset.mem_filter.mp he
    obtain ⟨t, ht, het⟩ := mem_packingEdges.mp (D.covers e (G.mem_edgeFinset.mp heG))
    exact Finset.mem_biUnion.mpr ⟨t,
      Finset.mem_filter.mpr ⟨ht, vertex_mem_of_triangleEdge het hv⟩, Finset.mem_filter.mpr ⟨het, hv⟩⟩

theorem TriangleDecomposition.vertex_count {G : SimpleGraph V} [DecidableRel G.Adj]
    (D : TriangleDecomposition G) (v : V) :
    2 * (D.triangles.filter (v ∈ ·)).card = G.degree v := by
  have hd : (D.triangles.filter (v ∈ ·) : Set (Finset V)).Pairwise
      (fun s t => Disjoint (vertexStar s v) (vertexStar t v)) := by
    intro s hs t ht hst
    exact (D.packing.2 (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp ht).1 hst).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hc := Finset.card_biUnion hd
  rw [D.vertex_stars, G.card_incidenceFinset_eq_degree] at hc
  rw [Finset.sum_congr rfl (fun t ht => vertexStar_card
    (D.packing.1 t (Finset.mem_filter.mp ht).1) (Finset.mem_filter.mp ht).2)] at hc
  simpa [mul_comm] using hc.symm

end ResearchMain.Tuza
