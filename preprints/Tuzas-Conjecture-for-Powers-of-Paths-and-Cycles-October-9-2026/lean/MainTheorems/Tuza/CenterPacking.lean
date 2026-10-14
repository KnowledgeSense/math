import MainTheorems.Tuza.FanCardinality

namespace ResearchMain.Tuza

def topEmbedding {V W : Type*} (e : V ↪ W) :
    (⊤ : SimpleGraph V) ↪g (⊤ : SimpleGraph W) where
  toEmbedding := e
  map_rel_iff' := by intro x y; exact not_congr e.injective.eq_iff

theorem add_center_packing {F V : Type*} [DecidableEq F] [DecidableEq V]
    {P : Finset (Finset (F ⊕ V))} (hP : Packing (fanGraph F V) P)
    {Q : Finset (Finset F)} (hQ : Packing (⊤ : SimpleGraph F) Q) :
    ∃ R : Finset (Finset (F ⊕ V)), Packing (⊤ : SimpleGraph (F ⊕ V)) R ∧
      R.card = P.card + Q.card := by
  let e : F ↪ F ⊕ V := Function.Embedding.inl
  let U := Q.map ⟨Finset.map e, Finset.map_injective _⟩
  have hU : Packing (⊤ : SimpleGraph (F ⊕ V)) U := hQ.map (topEmbedding e)
  have hPtop : Packing (⊤ : SimpleGraph (F ⊕ V)) P := hP.mono le_top
  have hcross : ∀ t ∈ P, ∀ u ∈ U, Disjoint (triangleEdges t) (triangleEdges u) := by
    intro t ht u hu
    obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hu
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    induction z using Sym2.inductionOn with
    | hf x y =>
      obtain ⟨hx, hy, _⟩ := mem_triangleEdges.mp hz'
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
      exact triangleEdges_subset (hP.1 t ht) _ hz
  refine ⟨P ∪ U, hPtop.union hU hcross, ?_⟩
  rw [hPtop.card_union hcross, Finset.card_map]

def twoCenterTriangles : Finset (Finset (Fin 5)) := {{0, 1, 4}, {2, 3, 4}}

theorem twoCenterTriangles_packing : Packing (⊤ : SimpleGraph (Fin 5)) twoCenterTriangles := by
  constructor
  · decide
  · decide

theorem twoCenterTriangles_card : twoCenterTriangles.card = 2 := by decide

def oneCenterTriangle : Finset (Finset (Fin 4)) := {{0, 1, 2}}

theorem oneCenterTriangle_packing : Packing (⊤ : SimpleGraph (Fin 4)) oneCenterTriangle := by
  constructor
  · decide
  · decide

theorem oneCenterTriangle_card : oneCenterTriangle.card = 1 := by decide

theorem complete_packing_transport {V : Type*} [Fintype V] [DecidableEq V]
    {P : Finset (Finset V)} (hP : Packing (⊤ : SimpleGraph V) P)
    (n : ℕ) (hcard : Fintype.card V = n) :
    ∃ Q : Finset (Finset (Fin n)), Packing (⊤ : SimpleGraph (Fin n)) Q ∧ Q.card = P.card := by
  classical
  let e : V ≃ Fin n := Fintype.equivOfCardEq (by simpa using hcard)
  let f : (⊤ : SimpleGraph V) ↪g (⊤ : SimpleGraph (Fin n)) := topEmbedding e.toEmbedding
  refine ⟨P.map ⟨Finset.map e.toEmbedding, Finset.map_injective _⟩, hP.map f, ?_⟩
  exact Finset.card_map _

end ResearchMain.Tuza
