import MainTheorems.Tuza.Constructions

namespace ResearchMain.Tuza

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

theorem triangleEdges_map (f : V ↪ W) (s : Finset V) :
    triangleEdges (s.map f) = (triangleEdges s).map f.sym2Map := by
  unfold triangleEdges
  rw [Finset.sym2_map, Finset.filter_map]
  congr 1
  apply Finset.filter_congr
  intro e _
  exact not_congr (Sym2.isDiag_map f.injective)

omit [DecidableEq V] [DecidableEq W] in
theorem clique_map {G : SimpleGraph V} {H : SimpleGraph W} {s : Finset V} {n : ℕ}
    (f : G ↪g H) (h : G.IsNClique n s) : H.IsNClique n (s.map f.toEmbedding) := by
  have hmap : G.map f.toEmbedding ≤ H :=
    SimpleGraph.map_le_of_le_comap (fun _ _ ht => f.map_rel_iff.mpr ht)
  exact (h.map).mono hmap

theorem Packing.map {G : SimpleGraph V} {H : SimpleGraph W} {P : Finset (Finset V)}
    (hP : Packing G P) (f : G ↪g H) :
    Packing H (P.map ⟨Finset.map f.toEmbedding, Finset.map_injective _⟩) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ht
    exact clique_map f (hP.1 s hs)
  · intro t ht u hu htu
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hu
    change Disjoint (triangleEdges (s.map f.toEmbedding))
      (triangleEdges (z.map f.toEmbedding))
    rw [triangleEdges_map, triangleEdges_map]
    apply (Finset.disjoint_map _).mpr
    exact hP.2 hs hz (fun heq => htu (congrArg (Finset.map f.toEmbedding) heq))

theorem Cover.map {G : SimpleGraph V} {H : SimpleGraph W} {C : Finset (Sym2 V)}
    (hC : Cover G C) (f : G ≃g H) : Cover H (C.map f.toEquiv.toEmbedding.sym2Map) := by
  refine ⟨?_, ?_⟩
  · intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp he
    have hedge := hC.1 d hd
    induction d using Sym2.inductionOn with
    | hf a b => exact f.map_rel_iff.mpr hedge
  · intro t ht
    let s := t.map f.symm.toEquiv.toEmbedding
    have hs : G.IsNClique 3 s := clique_map f.symm.toEmbedding ht
    have hback : s.map f.toEquiv.toEmbedding = t := by
      dsimp only [s]
      rw [Finset.map_map]
      have heq : f.symm.toEquiv.toEmbedding.trans f.toEquiv.toEmbedding =
          Function.Embedding.refl W := by
        ext x
        exact f.apply_symm_apply x
      rw [heq, Finset.map_refl]
    obtain ⟨e, he⟩ := hC.2 s hs
    obtain ⟨het, heC⟩ := Finset.mem_inter.mp he
    refine ⟨f.toEquiv.toEmbedding.sym2Map e, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [← hback, triangleEdges_map]
      exact Finset.mem_map.mpr ⟨e, het, rfl⟩
    · exact Finset.mem_map.mpr ⟨e, heC, rfl⟩

variable [Fintype V] [Fintype W]

theorem packingNumber_embedding_le {G : SimpleGraph V} {H : SimpleGraph W} (f : G ↪g H) :
    packingNumber G ≤ packingNumber H := by
  obtain ⟨P, hP, heq⟩ := exists_maximum_packing G
  have ht := packing_le_number (hP.map f)
  rw [Finset.card_map, heq] at ht
  exact ht

theorem packingNumber_iso {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    packingNumber G = packingNumber H :=
  Nat.le_antisymm (packingNumber_embedding_le f.toEmbedding) (packingNumber_embedding_le f.symm.toEmbedding)

theorem coverNumber_iso_le {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    coverNumber H ≤ coverNumber G := by
  obtain ⟨C, hC, heq⟩ := exists_minimum_cover G
  have ht := number_le_cover (hC.map f)
  rw [Finset.card_map, heq] at ht
  exact ht

theorem coverNumber_iso {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    coverNumber G = coverNumber H := Nat.le_antisymm (coverNumber_iso_le f.symm) (coverNumber_iso_le f)

theorem inequality_iso {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    Inequality G ↔ Inequality H := by
  rw [Inequality, Inequality, coverNumber_iso f, packingNumber_iso f]

end ResearchMain.Tuza
