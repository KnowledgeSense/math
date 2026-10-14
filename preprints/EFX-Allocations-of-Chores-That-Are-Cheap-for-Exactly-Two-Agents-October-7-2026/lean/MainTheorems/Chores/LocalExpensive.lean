import MainTheorems.Chores.SeparatedSystems

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

omit [DecidableEq E] in
theorem uniform_expensive_ge (M : TwoCheapModel A E) {f : E → A} {u v : A}
    (h : ∀ e ∈ bundle f u, ¬M.Cheap u e → ¬M.Cheap v e) :
    expensiveCount M f u u ≤ expensiveCount M f v u := by
  apply Finset.card_le_card
  intro e he
  obtain ⟨he, hc⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨he, h e he hc⟩

theorem uniform_expensive_strict (M : TwoCheapModel A E) {f : E → A} {u v : A}
    (huv : u ≠ v) (hm : Mixed M f u)
    (h : ∀ e ∈ bundle f u, ¬M.Cheap u e → ¬M.Cheap v e) :
    expensiveCount M f u u + 1 ≤ expensiveCount M f v u := by
  have hex : ∃ e ∈ bundle f u, M.Cheap u e ∧ ¬M.Cheap v e := by
    by_contra hn
    have hp : Pure M f u v := by
      intro e he hc
      by_contra hv
      exact hn ⟨e, he, hc, hv⟩
    exact pure_not_mixed M huv hp hm
  obtain ⟨d, hd, hdu, hdv⟩ := hex
  have hn : d ∉ (bundle f u).filter (fun e => ¬M.Cheap u e) := by simp [hdu]
  have hs : insert d ((bundle f u).filter (fun e => ¬M.Cheap u e)) ⊆
      (bundle f u).filter (fun e => ¬M.Cheap v e) := by
    intro e he
    rcases Finset.mem_insert.mp he with he | he
    · subst e
      exact Finset.mem_filter.mpr ⟨hd, hdv⟩
    · obtain ⟨he, hc⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨he, h e he hc⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem hn] at hc
  exact hc

theorem passed_vertex_margin (M : TwoCheapModel A E) {f : E → A} {u v : A} {d d' : ℕ}
    (huv : u ≠ v) (hm : Mixed M f u) (hcount : expensiveCount M f u u = d')
    (hlevel : d ≤ d') (h : ∀ e ∈ bundle f u, ¬M.Cheap u e → ¬M.Cheap v e) :
    d + 1 ≤ expensiveCount M f v u := by
  have ht := uniform_expensive_strict M huv hm h
  omega

end ResearchMain.Chores
