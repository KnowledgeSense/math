import MainTheorems.Chores.TokenSeed
import MainTheorems.Chores.RepairEFX

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace TokenSeed

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    {P : TokenReady M S f₀ q k}

theorem high_to_low (B : TokenSeed P) :
    expensiveCount M B.cycle.allocation P.high P.low = expensiveCount M P.allocation P.low P.low + 1 := by
  have ht := B.cycle.low_expensive_balance M P.high
  rw [ite_eq_left B.low_highCheap, add_zero,
    ite_eq_right (filler_not_cheap M P.high_mem B.high_filler)] at ht
  have hc := (minimum_bad_counts M (P.optimal.energyMinimum M) P.size
    P.high_mem P.low_mem P.unique_bad.1).2
  omega

theorem low_to_high (B : TokenSeed P) :
    expensiveCount M B.cycle.allocation P.low P.high = expensiveCount M P.allocation P.low P.low + 1 := by
  have hn := two_cheap_third M P.donor_high.symm B.donor_highCheap B.donor_ownCheap
    P.unique_bad.1.1.symm P.donor_low.symm
  have ht := B.cycle.high_expensive_balance M P.low
  rw [ite_eq_right (filler_not_cheap M P.low_mem B.high_filler), ite_eq_right hn,
    pure_observer_expensive M P.optimal.1.1 P.low_mem
      (optimal_bad_source_pure M P.optimal P.size P.high_mem P.low_mem P.unique_bad.1)] at ht
  have hc := (minimum_bad_counts M (P.optimal.energyMinimum M) P.size
    P.high_mem P.low_mem P.unique_bad.1).1
  omega

theorem pair_comparison (B : TokenSeed P) {r : ℝ} (hr : 2 < r) {v c : A}
    (hv : v = P.high ∨ v = P.low) (hc : c = P.high ∨ c = P.low) (hvc : v ≠ c) :
    threshold M r B.cycle.allocation v ≤ bundleCost M r v (bundle B.cycle.allocation c) := by
  apply positive_comparison M (by linarith : 1 ≤ r) (B.own_cheap (hv.elim Or.inl (fun ht => Or.inr (Or.inl ht))))
  · rw [B.cycle.card, B.cycle.card]
    have hl := (P.size c).1
    have hu := (P.size v).2
    omega
  · rcases hv with hv | hv <;> rcases hc with hc | hc <;> subst v <;> subst c
    · exact False.elim (hvc rfl)
    · rw [B.high_count, B.high_to_low]
      omega
    · rw [B.low_count, B.low_to_high]
    · exact False.elim (hvc rfl)

theorem pair_threshold (B : TokenSeed P) {r : ℝ} (hr : 2 < r) {v : A}
    (hv : v = P.high ∨ v = P.low) : threshold M r B.cycle.allocation v ≤ r * ((q : ℝ) - 2) + 2 := by
  have hown := B.own_cheap (hv.elim Or.inl (fun ht => Or.inr (Or.inl ht)))
  rw [positive_threshold M r hown, B.cycle.card]
  have hsize : ((bundle P.allocation v).card : ℝ) ≤ q + 1 := by exact_mod_cast (P.size v).2
  have hL : (expensiveCount M P.allocation P.low P.low : ℝ) + 3 ≤ q := by exact_mod_cast P.low_bound
  rcases hv with hv | hv <;> subst v
  · rw [B.high_count]
    nlinarith only [hsize, hL, hr]
  · rw [B.low_count]
    push_cast
    nlinarith only [hsize, hL, hr]

theorem low_whole (B : TokenSeed P) {v : A} (hv : v ∈ S)
    (hva : v ≠ P.high) (hvb : v ≠ P.low) :
    expensiveCount M B.cycle.allocation v P.low = (bundle B.cycle.allocation P.low).card := by
  have hn := two_cheap_third M P.unique_bad.1.1 B.low_highCheap B.low_ownCheap hva hvb
  have ht := B.cycle.low_expensive_balance M v
  rw [ite_eq_right hn, ite_eq_right (filler_not_cheap M hv B.high_filler),
    pure_outside_expensive M P.optimal.1.1 P.unique_bad.1.1.symm
      (minimum_bad_target_pure M (P.optimal.energyMinimum M) P.size
        P.high_mem P.low_mem P.unique_bad.1) hv hvb hva] at ht
  rw [B.cycle.card]
  omega

theorem high_near_whole (B : TokenSeed P) {v : A} (hv : v ∈ S)
    (hva : v ≠ P.high) (hvb : v ≠ P.low) :
    (bundle B.cycle.allocation P.high).card ≤ expensiveCount M B.cycle.allocation v P.high + 1 := by
  have ht := B.cycle.high_expensive_balance M v
  rw [ite_eq_right (filler_not_cheap M hv B.high_filler),
    pure_outside_expensive M P.optimal.1.1 P.unique_bad.1.1
      (optimal_bad_source_pure M P.optimal P.size P.high_mem P.low_mem P.unique_bad.1) hv hva hvb] at ht
  rw [B.cycle.card]
  split_ifs at ht <;> omega

theorem outsider_expensive (B : TokenSeed P) {v : A} (hv : v ∈ S)
    (hva : v ≠ P.high) (hvb : v ≠ P.low) (hvk : v ≠ k) (c : A) :
    expensiveCount M B.cycle.allocation v c = expensiveCount M P.allocation v c := by
  have hn₁ := filler_not_cheap M hv B.high_filler
  have hn₂ := two_cheap_third M P.unique_bad.1.1 B.low_highCheap B.low_ownCheap hva hvb
  have hn₃ := two_cheap_third M P.donor_high.symm B.donor_highCheap B.donor_ownCheap hva hvk
  by_cases hca : c = P.high
  · subst c
    have ht := B.cycle.high_expensive_balance M v
    rw [ite_eq_right hn₁, ite_eq_right hn₃] at ht
    omega
  · by_cases hcb : c = P.low
    · subst c
      have ht := B.cycle.low_expensive_balance M v
      rw [ite_eq_right hn₂, ite_eq_right hn₁] at ht
      omega
    · by_cases hck : c = k
      · subst c
        have ht := B.cycle.donor_expensive_balance M v
        rw [ite_eq_right hn₃, ite_eq_right hn₂] at ht
        omega
      · rw [expensiveCount, B.cycle.other_bundle hca hcb hck]
        rfl

theorem outsider_comparison (B : TokenSeed P) {r : ℝ} (hr : 2 < r) {v c : A}
    (hv : v ∈ S) (hva : v ≠ P.high) (hvb : v ≠ P.low) (hvk : v ≠ k) (hvc : v ≠ c) :
    threshold M r B.cycle.allocation v ≤ bundleCost M r v (bundle B.cycle.allocation c) := by
  have hθ : threshold M r B.cycle.allocation v = threshold M r P.allocation v :=
    threshold_eq_of_counts M r (B.cycle.card v) (B.outsider_expensive hv hva hvb hvk v)
  have hcost := cost_eq_of_counts M r (B.cycle.card c) (B.outsider_expensive hv hva hvb hvk c)
  rw [hθ, hcost]
  apply separated_comparison M hr (P.optimal.energyMinimum M) P.size hvc
  intro _ hcS hbad
  exact hva (P.unique_bad.2 v hv c hcS hbad).1

end TokenSeed

end ResearchMain.Chores
