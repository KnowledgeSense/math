import MainTheorems.Corona.BaseGraphs

namespace ResearchMain.Corona

def P4Free {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v w z, G.Adj u v → G.Adj v w → G.Adj w z →
    ¬G.Adj u w → ¬G.Adj u z → ¬G.Adj v z → False

theorem matching_two_neighbors (m : ℕ) {u v w : Fin m ⊕ (Fin m × Unit)}
    (huv : (matchingGraph m).Adj u v) (hvw : (matchingGraph m).Adj v w) : u = w := by
  rcases u with u | ⟨u, a⟩ <;> rcases v with v | ⟨v, b⟩ <;> rcases w with w | ⟨w, c⟩
  · exact False.elim huv
  · exact False.elim huv
  · change u = v at huv
    change v = w at hvw
    exact congrArg Sum.inl (huv.trans hvw)
  · exact False.elim hvw.2
  · exact False.elim hvw
  · change u = v at huv
    change v = w at hvw
    obtain rfl := huv.trans hvw
    exact congrArg (fun t => Sum.inr (u, t)) (Subsingleton.elim a c)
  · exact False.elim huv.2
  · exact False.elim huv.2

theorem matchingGraph_P4Free (m : ℕ) : P4Free (matchingGraph m) := by
  intro u v w z huv hvw hwz _ huz _
  obtain rfl := matching_two_neighbors m huv hvw
  exact huz hwz

theorem baseGraph_P4Free (a m : ℕ) : P4Free (baseGraph a m) := by
  rintro (u | u) (v | v) (w | w) (z | z) huv hvw hwz huw huz hvz
  all_goals try exact huw trivial
  all_goals try exact huz trivial
  all_goals try exact hvz trivial
  · exact False.elim huv
  · exact matchingGraph_P4Free m u v w z huv hvw hwz huw huz hvz

end ResearchMain.Corona
