import MainTheorems.Chores.PairCosts

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A]

theorem pure_of_equal_expensive (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) {a b : A} (ha : a ∈ S)
    (hcounts : expensiveCount M f a b = expensiveCount M f b b) : Pure M f b a := by
  have hsub : (bundle f b).filter (fun e => ¬M.Cheap b e) ⊆
      (bundle f b).filter (fun e => ¬M.Cheap a e) := by
    intro e he
    obtain ⟨he, hn⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨he, ?_⟩
    intro hc
    have ho := separated_owner_cheap M hf ha hc
    rw [(mem_bundle f b e).mp he] at ho
    exact hn ho
  have heq : (bundle f b).filter (fun e => ¬M.Cheap b e) =
      (bundle f b).filter (fun e => ¬M.Cheap a e) :=
    Finset.eq_of_subset_of_card_le hsub (by exact le_of_eq hcounts)
  intro e he hc
  by_contra hn
  have hmem : e ∈ (bundle f b).filter (fun e => ¬M.Cheap a e) := Finset.mem_filter.mpr ⟨he, hn⟩
  rw [← heq] at hmem
  exact (Finset.mem_filter.mp hmem).2 hc

end ResearchMain.Chores
