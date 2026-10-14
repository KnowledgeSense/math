import MainTheorems.Tuza.NestedRelation
import MainTheorems.Tuza.Transfer

namespace ResearchMain.Tuza

theorem IsCoChain.ferrers_representation {V : Type*} [Fintype V] {G : SimpleGraph V}
    (h : IsCoChain G) : ∃ a b : ℕ, ∃ d : FerrersProfile a b, Nonempty (d.graph ≃g G) := by
  classical
  obtain ⟨S, hS, hSc, hn⟩ := h
  let R : S → (Sᶜ : Set V) → Prop := fun x y => G.Adj x.val y.val
  have hnest : ∀ x x', rowSet R x ⊆ rowSet R x' ∨ rowSet R x' ⊆ rowSet R x := by
    intro x x'
    rcases hn x x.property x' x'.property with hh | hh
    · left
      intro y hy
      exact (mem_rowSet R _ _).mpr (hh y y.property ((mem_rowSet R _ _).mp hy))
    · right
      intro y hy
      exact (mem_rowSet R _ _).mpr (hh y y.property ((mem_rowSet R _ _).mp hy))
  obtain ⟨eA, eB, d, hd⟩ := exists_ferrers_ordering R hnest
  let e := (Equiv.sumCongr eA eB).trans (Equiv.Set.sumCompl S)
  refine ⟨Fintype.card S, Fintype.card (Sᶜ : Set V), d,
    ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩⟩
  intro x y
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      change G.Adj (eA i).val (eA j).val ↔ i ≠ j
      constructor
      · intro ha he
        exact ha.ne (congrArg (fun k => (eA k).val) he)
      · intro he
        exact hS (eA i).property (eA j).property
          (fun hv => he (eA.injective (Subtype.ext hv)))
    | inr j =>
      change R (eA i) (eB j) ↔ j.val < d.degree i
      exact hd i j
  | inr j =>
    cases y with
    | inl i =>
      change G.Adj (eB j).val (eA i).val ↔ j.val < d.degree i
      rw [G.adj_comm]
      exact hd i j
    | inr k =>
      change G.Adj (eB j).val (eB k).val ↔ j ≠ k
      constructor
      · intro ha he
        exact ha.ne (congrArg (fun l => (eB l).val) he)
      · intro he
        exact hSc (eB j).property (eB k).property
          (fun hv => he (eB.injective (Subtype.ext hv)))

theorem coChain_of_ferrers_inequality
    (hF : ∀ a b (d : FerrersProfile a b), Inequality d.graph)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : IsCoChain G) :
    Inequality G := by
  obtain ⟨a, b, d, ⟨e⟩⟩ := hG.ferrers_representation
  exact (inequality_iso e).mp (hF a b d)

end ResearchMain.Tuza
