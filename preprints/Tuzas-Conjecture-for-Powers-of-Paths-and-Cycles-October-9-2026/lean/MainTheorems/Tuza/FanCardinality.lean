import MainTheorems.Tuza.DecompositionAssembly

namespace ResearchMain.Tuza

instance {F V : Type*} [DecidableEq F] [DecidableEq V] : DecidableRel (fanGraph F V).Adj := by
  intro x y
  cases x <;> cases y
  all_goals unfold fanGraph
  all_goals infer_instance

theorem fanGraph_complement {F V : Type*} :
    fanGraph F V = (⊤ : SimpleGraph (F ⊕ V)) \
      imageGraph (⊤ : SimpleGraph F) Function.Embedding.inl := by
  ext x y
  cases x <;> cases y
  all_goals simp [fanGraph, imageGraph, Function.Embedding.inl_apply]

theorem fanGraph_card {F V : Type*} [Fintype F] [Fintype V] [DecidableEq F] [DecidableEq V] :
    (fanGraph F V).edgeFinset.card + (Fintype.card F).choose 2 =
      (Fintype.card F + Fintype.card V).choose 2 := by
  have hedge : (fanGraph F V).edgeFinset =
      ((⊤ : SimpleGraph (F ⊕ V)) \ imageGraph (⊤ : SimpleGraph F) Function.Embedding.inl).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [fanGraph_complement]
  rw [hedge, SimpleGraph.edgeFinset_sdiff]
  have hc := imageGraph_card_edges (⊤ : SimpleGraph F) (Function.Embedding.inl (β := V))
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two] at hc
  rw [← hc, Finset.card_sdiff_add_card_eq_card]
  · rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_sum]
  · exact SimpleGraph.edgeFinset_mono le_top

theorem fanGraph_degree_left {F V : Type*} [Fintype F] [Fintype V]
    [DecidableEq F] [DecidableEq V] (c : F) :
    (fanGraph F V).degree (.inl c) = Fintype.card V := by
  let e : (fanGraph F V).neighborSet (.inl c) ≃ V := {
    toFun := fun x => by
      obtain ⟨x, hx⟩ := x
      cases x with
      | inl _ => exact False.elim hx
      | inr v => exact v
    invFun := fun v => ⟨.inr v, trivial⟩
    left_inv := by intro x; obtain ⟨x, hx⟩ := x; cases x; exact False.elim hx; rfl
    right_inv := fun _ => rfl }
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr e]

end ResearchMain.Tuza
