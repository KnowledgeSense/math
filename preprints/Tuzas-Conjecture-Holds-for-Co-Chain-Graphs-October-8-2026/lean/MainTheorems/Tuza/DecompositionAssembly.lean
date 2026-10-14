import MainTheorems.Tuza.LatinTriangles

namespace ResearchMain.Tuza

variable {V W I : Type*} [DecidableEq V] [DecidableEq W]

theorem TriangleDecomposition.join {G H : SimpleGraph V}
    (D : TriangleDecomposition G) (E : TriangleDecomposition H)
    (hdis : ∀ x y, G.Adj x y → ¬H.Adj x y) :
    Nonempty (TriangleDecomposition (G ⊔ H)) := by
  have hcross : ∀ t ∈ D.triangles, ∀ u ∈ E.triangles,
      Disjoint (triangleEdges t) (triangleEdges u) := by
    intro t ht u hu
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    induction z using Sym2.inductionOn with
    | hf x y =>
      exact hdis x y (triangleEdges_subset (D.packing.1 t ht) _ hz)
        (triangleEdges_subset (E.packing.1 u hu) _ hz')
  refine ⟨⟨D.triangles ∪ E.triangles,
    (D.packing.mono le_sup_left).union (E.packing.mono le_sup_right) hcross, ?_⟩⟩
  intro z hz
  induction z using Sym2.inductionOn with
  | hf x y =>
    rcases hz with hz | hz
    · obtain ⟨t, ht, he⟩ := mem_packingEdges.mp (D.covers s(x, y) hz)
      exact mem_packingEdges.mpr ⟨t, Finset.mem_union_left _ ht, he⟩
    · obtain ⟨t, ht, he⟩ := mem_packingEdges.mp (E.covers s(x, y) hz)
      exact mem_packingEdges.mpr ⟨t, Finset.mem_union_right _ ht, he⟩

def imageGraph {V W : Type*} (G : SimpleGraph V) (f : V ↪ W) : SimpleGraph W where
  Adj x y := ∃ u v, f u = x ∧ f v = y ∧ G.Adj u v
  symm := ⟨by intro x y h; obtain ⟨u, v, hu, hv, huv⟩ := h; exact ⟨v, u, hv, hu, huv.symm⟩⟩
  loopless := ⟨by
    intro x h
    obtain ⟨u, v, hu, hv, huv⟩ := h
    exact huv.ne (f.injective (hu.trans hv.symm))⟩

instance {V W : Type*} [Fintype V] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V ↪ W) : DecidableRel (imageGraph G f).Adj := fun x y =>
  inferInstanceAs (Decidable (∃ u v, f u = x ∧ f v = y ∧ G.Adj u v))

theorem imageGraph_apply_adj {V W : Type*} (G : SimpleGraph V) (f : V ↪ W) (x y : V) :
    (imageGraph G f).Adj (f x) (f y) ↔ G.Adj x y := by
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    exact (f.injective hu) ▸ (f.injective hv) ▸ huv
  · intro h
    exact ⟨x, y, rfl, rfl, h⟩

theorem imageGraph_edgeFinset {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj] (f : V ↪ W) :
    (imageGraph G f).edgeFinset = G.edgeFinset.map f.sym2Map := by
  ext z
  induction z using Sym2.inductionOn with
  | hf x y =>
    constructor
    · intro hz
      obtain ⟨u, v, hu, hv, huv⟩ := (imageGraph G f).mem_edgeFinset.mp hz
      exact Finset.mem_map.mpr ⟨s(u, v), G.mem_edgeFinset.mpr huv, by simp [hu, hv]⟩
    · intro hz
      obtain ⟨e, he, heq⟩ := Finset.mem_map.mp hz
      induction e using Sym2.inductionOn with
      | hf u v =>
        have hi : s(f u, f v) ∈ (imageGraph G f).edgeSet :=
          ⟨u, v, rfl, rfl, G.mem_edgeFinset.mp he⟩
        exact (imageGraph G f).mem_edgeFinset.mpr (heq ▸ hi)

theorem imageGraph_card_edges {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj] (f : V ↪ W) :
    (imageGraph G f).edgeFinset.card = G.edgeFinset.card := by
  rw [imageGraph_edgeFinset, Finset.card_map]

theorem TriangleDecomposition.map {G : SimpleGraph V} (D : TriangleDecomposition G) (f : V ↪ W) :
    Nonempty (TriangleDecomposition (imageGraph G f)) := by
  let F : PackingFamily G D.triangles := {
    triangle := Subtype.val
    clique := fun t => D.packing.1 t.val t.property
    disjoint := fun t u htu => D.packing.2 t.property u.property
      (fun h => htu (Subtype.ext h)) }
  let M : PackingFamily (imageGraph G f) D.triangles :=
    F.map f (fun x y h => ⟨x, y, rfl, rfl, h⟩)
  refine ⟨⟨M.carrier, M.packing, ?_⟩⟩
  intro z hz
  induction z using Sym2.inductionOn with
  | hf x y =>
    obtain ⟨u, v, rfl, rfl, huv⟩ := hz
    obtain ⟨t, ht, he⟩ := mem_packingEdges.mp (D.covers s(u, v) huv)
    refine mem_packingEdges.mpr ⟨t.map f, Finset.mem_image.mpr ⟨⟨t, ht⟩,
      Finset.mem_univ _, rfl⟩, ?_⟩
    rw [triangleEdges_map]
    exact Finset.mem_map.mpr ⟨s(u, v), he, rfl⟩

theorem TriangleDecomposition.of_partition [Fintype I] {G : SimpleGraph V}
    (H : I → SimpleGraph V) (D : ∀ i, TriangleDecomposition (H i))
    (hle : ∀ i, H i ≤ G)
    (hdis : ∀ i j, i ≠ j → ∀ x y, (H i).Adj x y → ¬(H j).Adj x y)
    (hcovers : ∀ x y, G.Adj x y → ∃ i, (H i).Adj x y) :
    Nonempty (TriangleDecomposition G) := by
  classical
  let F : PackingFamily G (Σ i, (D i).triangles) := {
    triangle := fun t => t.2.val
    clique := fun t => ((D t.1).packing.1 t.2.val t.2.property).mono (hle t.1)
    disjoint := fun t u htu => by
      by_cases hi : t.1 = u.1
      · obtain ⟨i, t⟩ := t
        obtain ⟨j, u⟩ := u
        dsimp only at hi
        subst j
        exact (D i).packing.2 t.property u.property
          (fun h => htu (by congr 1; exact Subtype.ext h))
      · apply Finset.disjoint_left.mpr
        intro z hz hz'
        induction z using Sym2.inductionOn with
        | hf x y =>
          exact hdis t.1 u.1 hi x y
            (triangleEdges_subset ((D t.1).packing.1 t.2.val t.2.property) _ hz)
            (triangleEdges_subset ((D u.1).packing.1 u.2.val u.2.property) _ hz') }
  refine ⟨⟨F.carrier, F.packing, ?_⟩⟩
  intro z hz
  induction z using Sym2.inductionOn with
  | hf x y =>
    obtain ⟨i, hi⟩ := hcovers x y hz
    obtain ⟨t, ht, he⟩ := mem_packingEdges.mp ((D i).covers s(x, y) hi)
    exact mem_packingEdges.mpr ⟨t, Finset.mem_image.mpr ⟨⟨i, ⟨t, ht⟩⟩,
      Finset.mem_univ _, rfl⟩, he⟩

end ResearchMain.Tuza
