import MainTheorems.Chores.TokenWalkAdvance

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace TokenSeed

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    {P : TokenReady M S f₀ q k}

theorem walk_uniform (B : TokenSeed P) : ∀ t ∈ P.walkAgents, ∀ u ∈ P.walkAgents,
    ∀ e ∈ bundle B.cycle.allocation t, ¬M.Cheap t e → ¬M.Cheap u e := by
  intro t ht u hu e he hn
  obtain ⟨htS, hta, htb⟩ := P.mem_walkAgents.mp ht
  obtain ⟨huS, hua, hub⟩ := P.mem_walkAgents.mp hu
  have horiginal : e ∈ bundle P.allocation t → ¬M.Cheap u e := by
    intro he
    have hf := separated_expensive_filler M P.optimal.1.1 (e := e)
      (by rwa [(mem_bundle P.allocation t e).mp he])
    exact filler_not_cheap M huS hf
  by_cases htk : t = k
  · subst t
    rw [B.cycle.donor_bundle] at he
    rcases Finset.mem_insert.mp he with he | he
    · subst e
      exact two_cheap_third M P.unique_bad.1.1 B.low_highCheap B.low_ownCheap hua hub
    · exact horiginal (Finset.mem_of_mem_erase he)
  · rw [B.cycle.other_bundle hta htb htk] at he
    exact horiginal he

theorem walk_pair_margin (B : TokenSeed P) : ∀ p, p = P.high ∨ p = P.low → ∀ u ∈ P.walkAgents,
    expensiveCount M P.allocation P.low P.low + 1 ≤ expensiveCount M B.cycle.allocation p u := by
  intro p hp u hu
  obtain ⟨huS, hua, hub⟩ := P.mem_walkAgents.mp hu
  by_cases huk : u = k
  · subst u
    rcases hp with hp | hp <;> subst p
    · have ht := B.cycle.donor_expensive_balance M P.high
      rw [ite_eq_left B.donor_highCheap, ite_eq_left B.low_highCheap, add_zero, add_zero,
        P.high_observer] at ht
      exact le_of_eq ht.symm
    · have hn := two_cheap_third M P.donor_high.symm B.donor_highCheap B.donor_ownCheap
        P.unique_bad.1.1.symm P.donor_low.symm
      have hwhole := pure_outside_expensive M P.optimal.1.1 P.donor_high P.donor_pure
        P.low_mem P.donor_low.symm P.unique_bad.1.1.symm
      have ht := B.cycle.donor_expensive_balance M P.low
      rw [ite_eq_right hn, ite_eq_left B.low_ownCheap, add_zero, hwhole] at ht
      have hq := (P.size k).1
      have hL := P.low_bound
      omega
  · have heq : expensiveCount M B.cycle.allocation p u = expensiveCount M P.allocation p u := by
      rw [expensiveCount, B.cycle.other_bundle hua hub huk]
      rfl
    rw [heq]
    rcases hp with hp | hp <;> subst p
    · exact optimal_pair_high_margin M P.optimal P.size P.high_mem P.low_mem huS P.unique_bad.1 hua hub
    · exact optimal_pair_low_margin M P.optimal P.size P.high_mem P.low_mem huS P.unique_bad.1 hua hub

def initial_state (B : TokenSeed P) {r : ℝ} (hr : 2 < r) : TokenWalkState B r where
  allocation := B.cycle.allocation
  passed := ∅
  current := k
  predecessor := P.high
  passed_subset := Finset.empty_subset _
  current_mem := P.mem_walkAgents.mpr ⟨P.donor_mem, P.donor_high, P.donor_low⟩
  current_new := Finset.notMem_empty _
  predecessor_mem := Or.inl rfl
  predecessor_ne := P.donor_high
  card := B.cycle.card
  fixed := fun _ _ => rfl
  token_owner := B.cycle.token_owner
  uniform := B.walk_uniform
  current_count := by rw [B.donor_count, P.donor_count]
  current_bound := le_of_eq P.donor_count
  current_cheap := B.own_cheap (Or.inr (Or.inr rfl))
  current_anchor := Or.inr B.donor_pure
  passed_count := by simp
  passed_mixed := by simp
  passed_level := by simp
  passed_bound := by simp
  untouched := by
    intro u hu _ huk
    obtain ⟨_, hua, hub⟩ := P.mem_walkAgents.mp hu
    exact B.cycle.other_bundle hua hub huk
  donor_visited := Or.inr rfl
  internal := by
    intro u hu huk c _ huc
    obtain ⟨huS, hua, hub⟩ := P.mem_walkAgents.mp hu
    exact B.outsider_comparison hr huS hua hub huk huc
  pair_margin := B.walk_pair_margin

end TokenSeed

end ResearchMain.Chores
