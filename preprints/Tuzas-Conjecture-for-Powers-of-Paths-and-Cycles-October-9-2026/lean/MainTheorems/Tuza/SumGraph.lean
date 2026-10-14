import MainTheorems.Tuza.EdgeCounting

namespace ResearchMain.Tuza

variable {A B : Type*}

def sumInternalGraph (G : SimpleGraph A) (H : SimpleGraph B) : SimpleGraph (A ⊕ B) :=
  imageGraph G Function.Embedding.inl ⊔ imageGraph H Function.Embedding.inr

@[simp]
theorem sumInternalGraph_left (G : SimpleGraph A) (H : SimpleGraph B) (a a' : A) :
    (sumInternalGraph G H).Adj (.inl a) (.inl a') ↔ G.Adj a a' := by
  simp [sumInternalGraph, imageGraph, Function.Embedding.inl_apply, Function.Embedding.inr_apply]

@[simp]
theorem sumInternalGraph_right (G : SimpleGraph A) (H : SimpleGraph B) (b b' : B) :
    (sumInternalGraph G H).Adj (.inr b) (.inr b') ↔ H.Adj b b' := by
  simp [sumInternalGraph, imageGraph, Function.Embedding.inl_apply, Function.Embedding.inr_apply]

@[simp]
theorem sumInternalGraph_cross (G : SimpleGraph A) (H : SimpleGraph B) (a : A) (b : B) :
    ¬ (sumInternalGraph G H).Adj (.inl a) (.inr b) := by
  simp [sumInternalGraph, imageGraph, Function.Embedding.inl_apply, Function.Embedding.inr_apply]

@[simp]
theorem sumInternalGraph_cross_rev (G : SimpleGraph A) (H : SimpleGraph B) (a : A) (b : B) :
    ¬ (sumInternalGraph G H).Adj (.inr b) (.inl a) :=
  fun h => sumInternalGraph_cross G H a b h.symm

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

instance (G : SimpleGraph A) (H : SimpleGraph B) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (sumInternalGraph G H).Adj := by
  unfold sumInternalGraph
  infer_instance

theorem sumInternalGraph_card (G : SimpleGraph A) (H : SimpleGraph B)
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    (sumInternalGraph G H).edgeFinset.card = G.edgeFinset.card + H.edgeFinset.card := by
  have hd : ∀ x y, (imageGraph G Function.Embedding.inl).Adj x y →
      ¬ (imageGraph H Function.Embedding.inr).Adj x y := by
    rintro _ _ ⟨a, a', rfl, rfl, _⟩ ⟨b, b', hb, _, _⟩
    exact Sum.inr_ne_inl hb
  have he : (sumInternalGraph G H).edgeFinset =
      (imageGraph G Function.Embedding.inl ⊔ imageGraph H Function.Embedding.inr).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rfl
  rw [he, card_union_graph hd, imageGraph_card_edges, imageGraph_card_edges]

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem sumInternal_cross_disjoint (G : SimpleGraph A) (H : SimpleGraph B)
    (R : A → B → Prop) :
    ∀ x y, (sumInternalGraph G H).Adj x y → ¬ (crossRelationGraph R).Adj x y := by
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl a' => exact not_false
    | inr b => exact False.elim (sumInternalGraph_cross G H a b h)
  | inr b =>
    cases y with
    | inl a => exact False.elim (sumInternalGraph_cross G H a b h.symm)
    | inr b' => exact not_false

theorem sumInternal_cross_card (G : SimpleGraph A) (H : SimpleGraph B) (R : A → B → Prop)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel R] :
    (sumInternalGraph G H ⊔ crossRelationGraph R).edgeFinset.card =
      G.edgeFinset.card + H.edgeFinset.card + (crossRelationGraph R).edgeFinset.card := by
  rw [card_union_graph (sumInternal_cross_disjoint G H R), sumInternalGraph_card]

end ResearchMain.Tuza
