import MainTheorems.Tuza.SumGraph
import MainTheorems.Tuza.Transfer

namespace ResearchMain.PathCycleTuza

open Tuza

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def leftGraphEmbedding (G : SimpleGraph A) (H : SimpleGraph B) : G ↪g sumInternalGraph G H where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := fun {a b} => sumInternalGraph_left G H a b

def rightGraphEmbedding (G : SimpleGraph A) (H : SimpleGraph B) : H ↪g sumInternalGraph G H where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := fun {a b} => sumInternalGraph_right G H a b

omit [Fintype A] [Fintype B] in
theorem mapped_edges_disjoint (s : Finset A) (t : Finset B) :
    Disjoint (triangleEdges (s.map Function.Embedding.inl))
      (triangleEdges (t.map Function.Embedding.inr)) := by
  apply Finset.disjoint_left.mpr
  intro e hes het
  rw [triangleEdges_map] at hes het
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hes
  obtain ⟨b, hb, he⟩ := Finset.mem_map.mp het
  induction a using Sym2.inductionOn with
  | hf a a' =>
    induction b using Sym2.inductionOn with
    | hf b b' =>
      simp only [Function.Embedding.sym2Map_apply, Function.Embedding.inl_apply,
        Function.Embedding.inr_apply, Sym2.map_mk, Sym2.eq_iff,
        Sum.inr_ne_inl, false_and, or_self] at he

theorem sum_packing_bound (G : SimpleGraph A) (H : SimpleGraph B) :
    packingNumber G + packingNumber H ≤ packingNumber (sumInternalGraph G H) := by
  classical
  obtain ⟨P, hP, hPc⟩ := exists_maximum_packing G
  obtain ⟨Q, hQ, hQc⟩ := exists_maximum_packing H
  let PL : Finset (Finset (A ⊕ B)) := P.map ⟨Finset.map Function.Embedding.inl, Finset.map_injective _⟩
  let QR : Finset (Finset (A ⊕ B)) := Q.map ⟨Finset.map Function.Embedding.inr, Finset.map_injective _⟩
  have hPL : Packing (sumInternalGraph G H) PL := hP.map (leftGraphEmbedding G H)
  have hQR : Packing (sumInternalGraph G H) QR := hQ.map (rightGraphEmbedding G H)
  have hc : ∀ s ∈ PL, ∀ t ∈ QR, Disjoint (triangleEdges s) (triangleEdges t) := by
    intro s hs t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp ht
    exact mapped_edges_disjoint s t
  have hd : Disjoint PL QR := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨e, he⟩ := triangleEdges_nonempty (hPL.1 t ht)
    exact Finset.disjoint_left.mp (hc t ht t ht') he he
  have h := packing_le_number (hPL.union hQR hc)
  rw [Finset.card_union_of_disjoint hd] at h
  dsimp [PL, QR] at h
  rwa [Finset.card_map, Finset.card_map, hPc, hQc] at h

theorem mapped_cover_meets {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {C : Finset (Sym2 V)} (hC : Cover G C)
    {t : Finset V} (ht : G.IsNClique 3 t) (f : V ↪ W) :
    (triangleEdges (t.map f) ∩ C.map f.sym2Map).Nonempty := by
  obtain ⟨e, he⟩ := hC.2 t ht
  obtain ⟨het, heC⟩ := Finset.mem_inter.mp he
  refine ⟨f.sym2Map e, Finset.mem_inter.mpr ⟨?_, Finset.mem_map.mpr ⟨e, heC, rfl⟩⟩⟩
  rw [triangleEdges_map]
  exact Finset.mem_map.mpr ⟨e, het, rfl⟩

theorem sum_cover_bound (G : SimpleGraph A) (H : SimpleGraph B) :
    coverNumber (sumInternalGraph G H) ≤ coverNumber G + coverNumber H := by
  classical
  obtain ⟨C, hC, hCc⟩ := exists_minimum_cover G
  obtain ⟨D, hD, hDc⟩ := exists_minimum_cover H
  let CL : Finset (Sym2 (A ⊕ B)) := C.map Function.Embedding.inl.sym2Map
  let DR : Finset (Sym2 (A ⊕ B)) := D.map Function.Embedding.inr.sym2Map
  have hCD : Cover (sumInternalGraph G H) (CL ∪ DR) := by
    constructor
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · change e ∈ C.map Function.Embedding.inl.sym2Map at he
        obtain ⟨a, ha, hea⟩ := Finset.mem_map.mp he
        rw [← hea]
        have hg := hC.1 a ha
        induction a using Sym2.inductionOn with
        | hf a b => exact (sumInternalGraph_left G H a b).mpr hg
      · change e ∈ D.map Function.Embedding.inr.sym2Map at he
        obtain ⟨a, ha, hea⟩ := Finset.mem_map.mp he
        rw [← hea]
        have hg := hD.1 a ha
        induction a using Sym2.inductionOn with
        | hf a b => exact (sumInternalGraph_right G H a b).mpr hg
    · intro t ht
      obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := (sumInternalGraph G H).is3Clique_iff.mp ht
      cases x with
      | inl a =>
        cases y with
        | inr b => exact False.elim (sumInternalGraph_cross G H a b hxy)
        | inl b =>
          cases z with
          | inr c => exact False.elim (sumInternalGraph_cross G H a c hxz)
          | inl c =>
            have htG : G.IsNClique 3 {a, b, c} := G.is3Clique_iff.mpr ⟨a, b, c,
              (sumInternalGraph_left G H a b).mp hxy, (sumInternalGraph_left G H a c).mp hxz,
              (sumInternalGraph_left G H b c).mp hyz, rfl⟩
            obtain ⟨e, he⟩ := mapped_cover_meets (W := A ⊕ B) hC htG Function.Embedding.inl
            obtain ⟨het, heC⟩ := Finset.mem_inter.mp he
            refine ⟨e, Finset.mem_inter.mpr ⟨?_, Finset.mem_union_left _ heC⟩⟩
            simpa using het
      | inr a =>
        cases y with
        | inl b => exact False.elim (sumInternalGraph_cross_rev G H b a hxy)
        | inr b =>
          cases z with
          | inl c => exact False.elim (sumInternalGraph_cross_rev G H c a hxz)
          | inr c =>
            have htH : H.IsNClique 3 {a, b, c} := H.is3Clique_iff.mpr ⟨a, b, c,
              (sumInternalGraph_right G H a b).mp hxy, (sumInternalGraph_right G H a c).mp hxz,
              (sumInternalGraph_right G H b c).mp hyz, rfl⟩
            obtain ⟨e, he⟩ := mapped_cover_meets (W := A ⊕ B) hD htH Function.Embedding.inr
            obtain ⟨het, heD⟩ := Finset.mem_inter.mp he
            refine ⟨e, Finset.mem_inter.mpr ⟨?_, Finset.mem_union_right _ heD⟩⟩
            simpa using het
  have hc := number_le_cover hCD
  have hs := Finset.card_union_le CL DR
  have hCL : CL.card = coverNumber G := by rw [Finset.card_map, hCc]
  have hDR : DR.card = coverNumber H := by rw [Finset.card_map, hDc]
  omega

theorem sum_inequality (G : SimpleGraph A) (H : SimpleGraph B) (hG : Inequality G) (hH : Inequality H) :
    Inequality (sumInternalGraph G H) := by
  have hc := sum_cover_bound G H
  have hp := sum_packing_bound G H
  unfold Inequality at *
  omega

end ResearchMain.PathCycleTuza
