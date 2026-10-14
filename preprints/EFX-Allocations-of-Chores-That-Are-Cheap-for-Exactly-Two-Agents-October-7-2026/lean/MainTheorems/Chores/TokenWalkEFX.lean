import MainTheorems.Chores.TokenWalkState

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace TokenWalkState

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    {P : TokenReady M S f₀ q k} {B : TokenSeed P} {r : ℝ}

theorem pair_fixed (W : TokenWalkState B r) {p : A} (hp : p = P.high ∨ p = P.low) :
    bundle W.allocation p = bundle B.cycle.allocation p := by
  apply W.fixed
  intro ht
  obtain ⟨_, ha, hb⟩ := P.mem_walkAgents.mp ht
  exact hp.elim ha hb

theorem outside_fixed (W : TokenWalkState B r) {u : A} (hu : u ∉ S) :
    bundle W.allocation u = bundle P.allocation u := by
  have hua : u ≠ P.high := fun ht => hu (ht ▸ P.high_mem)
  have hub : u ≠ P.low := fun ht => hu (ht ▸ P.low_mem)
  have huk : u ≠ k := fun ht => hu (ht ▸ P.donor_mem)
  rw [W.fixed u (fun ht => hu (P.mem_walkAgents.mp ht).1)]
  exact B.cycle.other_bundle hua hub huk

theorem pair_cheap (W : TokenWalkState B r) {p : A} (hp : p = P.high ∨ p = P.low) :
    OwnCheap M W.allocation p := by
  unfold OwnCheap
  rw [W.pair_fixed hp]
  exact B.own_cheap (hp.elim Or.inl (fun ht => Or.inr (Or.inl ht)))

theorem pair_count_le (W : TokenWalkState B r) {p : A} (hp : p = P.high ∨ p = P.low) :
    expensiveCount M W.allocation p p ≤ expensiveCount M P.allocation P.low P.low + 1 := by
  have heq : expensiveCount M W.allocation p p = expensiveCount M B.cycle.allocation p p := by
    rw [expensiveCount, W.pair_fixed hp]
    rfl
  rw [heq]
  rcases hp with hp | hp <;> subst p
  · rw [B.high_count]
    omega
  · rw [B.low_count]

theorem pair_to_other (W : TokenWalkState B r) (hr : 2 < r) {p c : A}
    (hp : p = P.high ∨ p = P.low) (hc : c ≠ P.high ∧ c ≠ P.low) :
    threshold M r W.allocation p ≤ bundleCost M r p (bundle W.allocation c) := by
  apply positive_comparison M (by linarith : 1 ≤ r) (W.pair_cheap hp)
  · have h₁ := (W.balanced p).2
    have h₂ := (W.balanced c).1
    omega
  · apply (W.pair_count_le hp).trans
    by_cases hcS : c ∈ S
    · exact W.pair_margin p hp c (P.mem_walkAgents.mpr ⟨hcS, hc⟩)
    · have hpS : p ∈ S := hp.elim (fun ht => ht ▸ P.high_mem) (fun ht => ht ▸ P.low_mem)
      have heq : expensiveCount M W.allocation p c = (bundle P.allocation c).card := by
        rw [expensiveCount, W.outside_fixed hcS]
        exact separated_outside_target_expensive M P.optimal.1.1 hpS hcS
      rw [heq]
      have ht := (P.size c).1
      have hL := P.low_bound
      omega

theorem walk_to_outside (W : TokenWalkState B r) (hr : 2 < r) {u c : A}
    (hu : u ∈ P.walkAgents) (hc : c ∉ S) :
    threshold M r W.allocation u ≤ bundleCost M r u (bundle W.allocation c) := by
  have hθ := threshold_le_balanced M hr W.balanced u
  have heq : expensiveCount M W.allocation u c = (bundle W.allocation c).card := by
    rw [expensiveCount, W.outside_fixed hc]
    exact separated_outside_target_expensive M P.optimal.1.1 (P.mem_walkAgents.mp hu).1 hc
  exact hθ.trans (expensive_lower_cost M hr (W.balanced c).1 (by rw [heq]; exact (W.balanced c).1))

theorem visited_threshold (W : TokenWalkState B r) (hr : 2 < r) {u : A}
    (hu : u ∈ W.passed ∨ u = W.current) :
    threshold M r W.allocation u ≤ r * ((q : ℝ) - 1) + 1 := by
  have hown : OwnCheap M W.allocation u := by
    rcases hu with hu | hu
    · obtain ⟨e, he, _, _, hc, _, _⟩ := W.passed_mixed u hu
      exact ⟨e, he, hc⟩
    · subst u
      exact W.current_cheap
  have he : expensiveCount M W.allocation u u ≤ q - 1 := by
    have hL := P.low_bound
    rcases hu with hu | hu
    · rw [W.passed_count u hu]
      have hd := W.passed_bound u hu
      omega
    · subst u
      rw [W.current_count]
      have hd := W.current_bound
      omega
  have hsz : ((bundle W.allocation u).card : ℝ) ≤ q + 1 := by exact_mod_cast (W.balanced u).2
  have he' : (expensiveCount M W.allocation u u : ℝ) ≤ (q : ℝ) - 1 := by
    have ht : expensiveCount M W.allocation u u + 1 ≤ q := by
      have hL := P.low_bound
      omega
    have ht' : (expensiveCount M W.allocation u u : ℝ) + 1 ≤ q := by exact_mod_cast ht
    linarith
  rw [positive_threshold M r hown]
  nlinarith only [hsz, he', hr]

theorem walk_to_pair (W : TokenWalkState B r) (hr : 2 < r) {u p : A}
    (hu : u ∈ P.walkAgents) (hp : p = P.high ∨ p = P.low) :
    threshold M r W.allocation u ≤ bundleCost M r u (bundle W.allocation p) := by
  obtain ⟨huS, hua, hub⟩ := P.mem_walkAgents.mp hu
  by_cases hvis : u ∈ W.passed ∨ u = W.current
  · have hnear : q ≤ expensiveCount M W.allocation u p + 1 := by
      have heq : expensiveCount M W.allocation u p = expensiveCount M B.cycle.allocation u p := by
        rw [expensiveCount, W.pair_fixed hp]
        rfl
      rw [heq]
      rcases hp with hp | hp <;> subst p
      · have ht := B.high_near_whole huS hua hub
        have hq := (P.size P.high).1
        rw [B.cycle.card] at ht
        omega
      · rw [B.low_whole huS hua hub, B.cycle.card]
        have hq := (P.size P.low).1
        omega
    exact (W.visited_threshold hr hvis).trans (near_whole_cost M hr (W.balanced p).1 hnear)
  · have hup : u ∉ W.passed := fun ht => hvis (Or.inl ht)
    have huc : u ≠ W.current := fun ht => hvis (Or.inr ht)
    have huk : u ≠ k := by
      intro ht
      subst u
      exact W.donor_visited.elim (fun h => hup h) huc
    have hθ : threshold M r W.allocation u = threshold M r P.allocation u := by
      apply threshold_eq_of_counts M r (W.card u)
      rw [expensiveCount, W.untouched u hu hup huc]
      rfl
    have heq : expensiveCount M W.allocation u p = expensiveCount M P.allocation u p := by
      rw [expensiveCount, W.pair_fixed hp]
      exact B.outsider_expensive huS hua hub huk p
    have hwhole : expensiveCount M P.allocation u p = (bundle P.allocation p).card := by
      rcases hp with hp | hp <;> subst p
      · exact pure_outside_expensive M P.optimal.1.1 P.unique_bad.1.1
          (optimal_bad_source_pure M P.optimal P.size P.high_mem P.low_mem P.unique_bad.1)
          huS hua hub
      · exact pure_outside_expensive M P.optimal.1.1 P.unique_bad.1.1.symm
          (minimum_bad_target_pure M (P.optimal.energyMinimum M) P.size
            P.high_mem P.low_mem P.unique_bad.1) huS hub hua
    rw [hθ]
    exact (threshold_le_balanced M hr P.size u).trans
      (expensive_lower_cost M hr (W.balanced p).1 (by rw [heq, hwhole]; exact (P.size p).1))

theorem outside_comparison (W : TokenWalkState B r) (hr : 2 < r) {u c : A} (hu : u ∉ S) :
    threshold M r W.allocation u ≤ bundleCost M r u (bundle W.allocation c) := by
  have hθ : threshold M r W.allocation u = threshold M r P.allocation u := by
    apply threshold_eq_of_counts M r (W.card u)
    rw [expensiveCount, W.outside_fixed hu]
    rfl
  rw [hθ]
  have ht := separated_outside_threshold M P.optimal.1.1 r P.size hu
  have hq : (q : ℝ) ≤ (bundle W.allocation c).card := by exact_mod_cast (W.balanced c).1
  exact ht.trans (hq.trans (cost_ge_size M (by linarith : 1 ≤ r) W.allocation u c))

theorem terminal_efx (W : TokenWalkState B r) (hr : 2 < r)
    (hstop : ∀ w ∈ P.walkAgents, W.current ≠ w →
      expensiveCount M P.allocation W.current W.current + 1 ≤
        expensiveCount M W.allocation W.current w) : EFX M r W.allocation := by
  rw [efx_iff_threshold M hr]
  intro u c huc
  by_cases huS : u ∈ S
  · by_cases hup : u = P.high ∨ u = P.low
    · by_cases hcp : c = P.high ∨ c = P.low
      · have hθ : threshold M r W.allocation u = threshold M r B.cycle.allocation u := by
          apply threshold_eq_of_counts M r
          · rw [W.pair_fixed hup]
          · rw [expensiveCount, W.pair_fixed hup]
            rfl
        rw [hθ, W.pair_fixed hcp]
        exact B.pair_comparison hr hup hcp huc
      · exact W.pair_to_other hr hup ⟨fun h => hcp (Or.inl h), fun h => hcp (Or.inr h)⟩
    · have hu : u ∈ P.walkAgents := P.mem_walkAgents.mpr
        ⟨huS, fun h => hup (Or.inl h), fun h => hup (Or.inr h)⟩
      by_cases hcS : c ∈ S
      · by_cases hcp : c = P.high ∨ c = P.low
        · exact W.walk_to_pair hr hu hcp
        · have hc : c ∈ P.walkAgents := P.mem_walkAgents.mpr
            ⟨hcS, fun h => hcp (Or.inl h), fun h => hcp (Or.inr h)⟩
          by_cases huv : u = W.current
          · subst u
            apply positive_comparison M (by linarith : 1 ≤ r) W.current_cheap
            · have h₁ := (W.balanced W.current).2
              have h₂ := (W.balanced c).1
              omega
            · rw [W.current_count]
              exact hstop c hc huc
          · exact W.internal u hu huv c hc huc
      · exact W.walk_to_outside hr hu hcS
  · exact W.outside_comparison hr huS

end TokenWalkState

end ResearchMain.Chores
