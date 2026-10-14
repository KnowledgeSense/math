import MainTheorems.Tuza.Basic

namespace ResearchMain.Tuza

variable {V : Type*} [DecidableEq V]

theorem triangleEdges_triple {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    triangleEdges {a, b, c} = {s(a, b), s(a, c), s(b, c)} := by
  ext e
  induction e using Sym2.inductionOn with
  | hf x y =>
    simp only [mem_triangleEdges, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    grind

theorem triangleEdges_card {G : SimpleGraph V} {t : Finset V} (ht : G.IsNClique 3 t) :
    (triangleEdges t).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := G.is3Clique_iff.mp ht
  rw [triangleEdges_triple hab.ne hac.ne hbc.ne]
  simp [hab.ne, hac.ne, hbc.ne, hab.ne.symm, hbc.ne.symm]

def packingEdges (P : Finset (Finset V)) : Finset (Sym2 V) := P.biUnion triangleEdges

@[simp]
theorem mem_packingEdges {P : Finset (Finset V)} {e : Sym2 V} :
    e ∈ packingEdges P ↔ ∃ t ∈ P, e ∈ triangleEdges t := Finset.mem_biUnion

theorem Packing.card_edges {G : SimpleGraph V} {P : Finset (Finset V)} (hP : Packing G P) :
    (packingEdges P).card = 3 * P.card := by
  unfold packingEdges
  rw [Finset.card_biUnion hP.2]
  rw [Finset.sum_congr rfl (fun t ht => triangleEdges_card (hP.1 t ht))]
  simp [mul_comm]

theorem Packing.edges_subset {G : SimpleGraph V} {P : Finset (Finset V)} (hP : Packing G P) :
    ∀ e ∈ packingEdges P, e ∈ G.edgeSet := by
  intro e he
  obtain ⟨t, ht, het⟩ := mem_packingEdges.mp he
  exact triangleEdges_subset (hP.1 t ht) e het

theorem Packing.card_union {G : SimpleGraph V} {P Q : Finset (Finset V)}
    (hP : Packing G P)
    (hcross : ∀ t ∈ P, ∀ u ∈ Q, Disjoint (triangleEdges t) (triangleEdges u)) :
    (P ∪ Q).card = P.card + Q.card := by
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_left.mpr
  intro t htP htQ
  obtain ⟨e, he⟩ := triangleEdges_nonempty (hP.1 t htP)
  exact Finset.disjoint_left.mp (hcross t htP t htQ) he he

structure TriangleDecomposition (G : SimpleGraph V) where
  triangles : Finset (Finset V)
  packing : Packing G triangles
  covers : ∀ e, e ∈ G.edgeSet → e ∈ packingEdges triangles

theorem TriangleDecomposition.edges [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (D : TriangleDecomposition G) : packingEdges D.triangles = G.edgeFinset := by
  ext e
  exact ⟨fun he => G.mem_edgeFinset.mpr (D.packing.edges_subset e he),
    fun he => D.covers e (G.mem_edgeFinset.mp he)⟩

theorem TriangleDecomposition.card [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (D : TriangleDecomposition G) : 3 * D.triangles.card = G.edgeFinset.card := by
  rw [← D.packing.card_edges, D.edges]

end ResearchMain.Tuza
