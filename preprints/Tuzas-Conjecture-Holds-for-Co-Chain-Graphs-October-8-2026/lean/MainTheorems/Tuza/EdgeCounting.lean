import MainTheorems.Tuza.DecompositionAssembly

namespace ResearchMain.Tuza

variable {V A B : Type*}

def crossEdgeEmbedding : A × B ↪ Sym2 (A ⊕ B) where
  toFun p := s(Sum.inl p.1, Sum.inr p.2)
  inj' := by
    intro p q hpq
    simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, or_false] at hpq
    exact Prod.ext hpq.1 hpq.2

@[simp]
theorem crossEdgeEmbedding_apply (p : A × B) :
    crossEdgeEmbedding p = s(Sum.inl p.1, Sum.inr p.2) := rfl

def crossRelationGraph (R : A → B → Prop) : SimpleGraph (A ⊕ B) where
  Adj x y := match x, y with
    | .inl a, .inr b => R a b
    | .inr b, .inl a => R a b
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> exact id⟩
  loopless := ⟨by intro x; cases x <;> exact id⟩

instance (R : A → B → Prop) [DecidableRel R] :
    DecidableRel (crossRelationGraph R).Adj := by
  intro x y
  cases x <;> cases y <;> unfold crossRelationGraph <;> dsimp <;> infer_instance

variable [Fintype A] [Fintype B]

theorem crossRelationGraph_edges (R : A → B → Prop) [DecidableRel R] :
    (crossRelationGraph R).edgeFinset =
      (Finset.univ.filter (fun p : A × B => R p.1 p.2)).map crossEdgeEmbedding := by
  ext e
  rw [SimpleGraph.mem_edgeFinset]
  induction e using Sym2.inductionOn with
  | hf x y =>
    cases x with
    | inl a =>
      cases y with
      | inl a' => simp [crossRelationGraph, Finset.mem_map]
      | inr b => simp [crossRelationGraph, Finset.mem_map]
    | inr b =>
      cases y with
      | inl a => simp [crossRelationGraph, Finset.mem_map]
      | inr b' => simp [crossRelationGraph, Finset.mem_map]

theorem crossRelationGraph_card (R : A → B → Prop) [DecidableRel R] :
    (crossRelationGraph R).edgeFinset.card =
      (Finset.univ.filter (fun p : A × B => R p.1 p.2)).card := by
  rw [crossRelationGraph_edges, Finset.card_map]

theorem crossRelationGraph_card_le (R : A → B → Prop) [DecidableRel R] :
    (crossRelationGraph R).edgeFinset.card ≤ Fintype.card A * Fintype.card B := by
  rw [crossRelationGraph_card]
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_prod A B)

variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem edgeFinset_disjoint {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : ∀ x y, G.Adj x y → ¬ H.Adj x y) : Disjoint G.edgeFinset H.edgeFinset := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  induction e using Sym2.inductionOn with
  | hf x y => exact h x y (G.mem_edgeFinset.mp he) (H.mem_edgeFinset.mp he')

theorem card_union_graph {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : ∀ x y, G.Adj x y → ¬ H.Adj x y) :
    (G ⊔ H).edgeFinset.card = G.edgeFinset.card + H.edgeFinset.card := by
  rw [SimpleGraph.edgeFinset_sup, Finset.card_union_of_disjoint (edgeFinset_disjoint h)]

end ResearchMain.Tuza
