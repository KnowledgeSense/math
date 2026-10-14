import MainTheorems.Tuza.LatinTriangles

namespace ResearchMain.Tuza

variable {V Q : Type*} [DecidableEq V] [DecidableEq Q] [Fintype Q] [AddCommGroup Q]

omit [DecidableEq V] in
theorem triangle_coordinates {t : Finset V} (ht : t.card = 3) :
    ∃ e : Fin 3 ↪ V, (∀ i, e i ∈ t) ∧ ∀ x ∈ t, ∃ i, e i = x := by
  classical
  let e : Fin 3 ≃ t := Fintype.equivOfCardEq (by simp [ht])
  refine ⟨e.toEmbedding.trans (Function.Embedding.subtype (· ∈ t)), ?_, ?_⟩
  · intro i
    exact (e i).property
  · intro x hx
    exact ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩

theorem exists_blowup_decomposition {G : SimpleGraph V} (D : TriangleDecomposition G) :
    Nonempty (TriangleDecomposition (crossGraph G Q)) := by
  classical
  have hcoord (t : D.triangles) := triangle_coordinates (D.packing.1 t.val t.property).2
  choose e hmem hsur using hcoord
  let T (i : D.triangles × (Q × Q)) :=
    (latinTriangle i.2.1 i.2.2).map (latinEmbedding (e i.1))
  have hclique (i : D.triangles × (Q × Q)) : (crossGraph G Q).IsNClique 3 (T i) := by
    apply clique_map_of_adj (latinEmbedding (e i.1)) ?_ (latinTriangle_clique i.2.1 i.2.2)
    intro x y hxy
    exact (D.packing.1 i.1.val i.1.property).1 (hmem i.1 x.1) (hmem i.1 y.1)
      (fun h => hxy ((e i.1).injective h))
  let F : PackingFamily (crossGraph G Q) (D.triangles × (Q × Q)) := {
    triangle := T
    clique := hclique
    disjoint := fun i j hij => by
      by_cases ht : i.1 = j.1
      · have hkey : i.2 ≠ j.2 := by
          intro he
          exact hij (Prod.ext ht he)
        dsimp only [T]
        rw [ht, triangleEdges_map, triangleEdges_map]
        exact (Finset.disjoint_map (latinEmbedding (e j.1)).sym2Map).mpr
          (latinTriangle_disjoint hkey)
      · apply Finset.disjoint_left.mpr
        intro z hzi hzj
        induction z using Sym2.inductionOn with
        | hf x y =>
          have hi := mapped_latinTriangle_base_edge (e i.1) (hmem i.1) hzi
          have hj := mapped_latinTriangle_base_edge (e j.1) (hmem j.1) hzj
          exact Finset.disjoint_left.mp
            (D.packing.2 i.1.property j.1.property (fun he => ht (Subtype.ext he))) hi hj }
  refine ⟨⟨F.carrier, F.packing, ?_⟩⟩
  intro z hz
  induction z using Sym2.inductionOn with
  | hf x y =>
    change G.Adj x.1 y.1 at hz
    obtain ⟨t, ht, hbase⟩ := mem_packingEdges.mp (D.covers s(x.1, y.1) hz)
    obtain ⟨hxt, hyt, _⟩ := mem_triangleEdges.mp hbase
    obtain ⟨i, hi⟩ := hsur ⟨t, ht⟩ x.1 hxt
    obtain ⟨j, hj⟩ := hsur ⟨t, ht⟩ y.1 hyt
    have hij : i ≠ j := by
      intro he
      exact hz.ne (hi.symm.trans (he ▸ hj))
    obtain ⟨u, v, hui, hvj⟩ := exists_latin_labels hij x.2 y.2
    let k : D.triangles × (Q × Q) := (⟨t, ht⟩, u, v)
    apply mem_packingEdges.mpr
    refine ⟨T k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩, ?_⟩
    apply mem_triangleEdges.mpr
    refine ⟨?_, ?_, fun h => hz.ne (congrArg Prod.fst h)⟩
    · exact (mem_mapped_latinTriangle (e ⟨t, ht⟩) u v x).mpr ⟨i, hi, hui.symm⟩
    · exact (mem_mapped_latinTriangle (e ⟨t, ht⟩) u v y).mpr ⟨j, hj, hvj.symm⟩

end ResearchMain.Tuza
