import MainTheorems.Chores.RepairStats

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

omit [DecidableEq E] in
theorem near_whole_cost (M : TwoCheapModel A E) {f : E → A} {v c : A} {q : ℕ}
    {r : ℝ} (hr : 2 < r) (hs : q ≤ (bundle f c).card)
    (he : q ≤ expensiveCount M f v c + 1) :
    r * ((q : ℝ) - 1) + 1 ≤ bundleCost M r v (bundle f c) := by
  have hs' : (q : ℝ) ≤ (bundle f c).card := by exact_mod_cast hs
  have he' : (q : ℝ) ≤ expensiveCount M f v c + 1 := by exact_mod_cast he
  rw [bundleCost_eq_size]
  nlinarith only [hs', he', hr]

omit [DecidableEq E] in
theorem expensive_lower_cost (M : TwoCheapModel A E) {f : E → A} {v c : A} {q : ℕ}
    {r : ℝ} (hr : 2 < r) (hs : q ≤ (bundle f c).card)
    (he : q ≤ expensiveCount M f v c) :
    r * q ≤ bundleCost M r v (bundle f c) := by
  have hs' : (q : ℝ) ≤ (bundle f c).card := by exact_mod_cast hs
  have he' : (q : ℝ) ≤ expensiveCount M f v c := by exact_mod_cast he
  rw [bundleCost_eq_size]
  nlinarith only [hs', he', hr]

theorem repaired_pairs_efx (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f g : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hordinary : ∀ i : PairIndex M S f, expensiveCount M f i.low i.low + 1 ≠ q →
      OrdinaryStats M f g i.high i.low)
    (hspecial : ∀ i : PairIndex M S f, expensiveCount M f i.low i.low + 1 = q →
      SpecialStats M g i.high i.low q)
    (hother : ∀ v, (∀ i : PairIndex M S f, v ≠ i.high ∧ v ≠ i.low) →
      bundle g v = bundle f v)
    (hcross : ∀ i j : PairIndex M S f, i ≠ j → ∀ v c,
      (v = i.high ∨ v = i.low) → (c = j.high ∨ c = j.low) →
      (expensiveCount M f i.low i.low + 1 = q → q ≤ expensiveCount M g v c) ∧
      (expensiveCount M f i.low i.low + 1 ≠ q → q ≤ expensiveCount M g v c + 1))
    (houtside : ∀ v ∈ S, (∀ i : PairIndex M S f, v ≠ i.high ∧ v ≠ i.low) →
      ∀ i : PairIndex M S f, ∀ c, (c = i.high ∨ c = i.low) →
      (expensiveCount M f i.low i.low + 1 = q → expensiveCount M g v c = (bundle g c).card) ∧
      (expensiveCount M f i.low i.low + 1 ≠ q → expensiveCount M g v c = expensiveCount M f v c)) :
    EFX M r g := by
  have hr1 : 1 ≤ r := by linarith
  have hmin (c : A) : q ≤ (bundle g c).card := by
    by_cases hc : ∃ i : PairIndex M S f, c = i.high ∨ c = i.low
    · obtain ⟨i, hc⟩ := hc
      by_cases hi : expensiveCount M f i.low i.low + 1 = q
      · have B := hspecial i hi
        rcases hc with hc | hc <;> subst c
        · rw [B.high_size]
        · rw [B.low_size]
          omega
      · rw [(hordinary i hi).size c hc]
        exact (hs c).1
    · rw [hother c (fun i => ⟨fun h => hc ⟨i, Or.inl h⟩, fun h => hc ⟨i, Or.inr h⟩⟩)]
      exact (hs c).1
  rw [efx_iff_threshold M hr]
  intro v c hvc
  by_cases hv : ∃ i : PairIndex M S f, v = i.high ∨ v = i.low
  · obtain ⟨i, hv⟩ := hv
    have hvS : v ∈ S := hv.elim (fun h => h ▸ i.members.1) (fun h => h ▸ i.members.2)
    by_cases hc : c = i.high ∨ c = i.low
    · by_cases hi : expensiveCount M f i.low i.low + 1 = q
      · exact (hspecial i hi).mutual_comparison hr hv hc hvc
      · have B := hordinary i hi
        apply positive_comparison M hr1 (B.cheap v hv)
        · rw [B.size v hv, B.size c hc]
          have hl := (hs c).1
          have hu := (hs v).2
          omega
        · exact B.comparison_expensive v c hv hc hvc
    · have hca : c ≠ i.high := fun h => hc (Or.inl h)
      have hcb : c ≠ i.low := fun h => hc (Or.inr h)
      by_cases hcp : ∃ j : PairIndex M S f, c = j.high ∨ c = j.low
      · obtain ⟨j, hj⟩ := hcp
        have hij : i ≠ j := fun h => hc (h ▸ hj)
        by_cases hi : expensiveCount M f i.low i.low + 1 = q
        · exact ((hspecial i hi).threshold_bound hr hv).trans
            (expensive_lower_cost M hr (hmin c) ((hcross i j hij v c hv hj).1 hi))
        · have hL := (optimal_ordinary_pair M hf hs i.members.1 i.members.2 i.bad hi).2
          exact ((hordinary i hi).threshold_bound hr (fun c => (hs c).2) hL hv).trans
            (near_whole_cost M hr (hmin c) ((hcross i j hij v c hv hj).2 hi))
      · have hcn : ∀ j : PairIndex M S f, c ≠ j.high ∧ c ≠ j.low :=
          fun j => ⟨fun h => hcp ⟨j, Or.inl h⟩, fun h => hcp ⟨j, Or.inr h⟩⟩
        have hcE : expensiveCount M g v c = expensiveCount M f v c := by
          rw [expensiveCount, hother c hcn]
          rfl
        have hmargin : expensiveCount M f i.low i.low + 1 ≤ expensiveCount M f v c := by
          by_cases hcS : c ∈ S
          · rcases hv with hv | hv <;> subst v
            · exact optimal_pair_high_margin M hf hs i.members.1 i.members.2 hcS i.bad hca hcb
            · exact optimal_pair_low_margin M hf hs i.members.1 i.members.2 hcS i.bad hca hcb
          · rw [separated_outside_target_expensive M hf.1.1 hvS hcS]
            have hL := optimal_bad_expensive_bound M hf hs i.members.1 i.members.2 i.bad
            have hsz := (hs c).1
            omega
        by_cases hi : expensiveCount M f i.low i.low + 1 = q
        · have he : q ≤ expensiveCount M g v c := by rw [hcE]; omega
          exact ((hspecial i hi).threshold_bound hr hv).trans (expensive_lower_cost M hr (hmin c) he)
        · have B := hordinary i hi
          apply positive_comparison M hr1 (B.cheap v hv)
          · rw [B.size v hv, hother c hcn]
            have hl := (hs c).1
            have hu := (hs v).2
            omega
          · rw [B.expensive v hv, hcE]
            exact hmargin
  · have hvn : ∀ i : PairIndex M S f, v ≠ i.high ∧ v ≠ i.low :=
      fun i => ⟨fun h => hv ⟨i, Or.inl h⟩, fun h => hv ⟨i, Or.inr h⟩⟩
    have ht : threshold M r g v = threshold M r f v := by
      apply threshold_eq_of_counts M r
      · rw [hother v hvn]
      · rw [expensiveCount, hother v hvn]
        rfl
    rw [ht]
    by_cases hvS : v ∈ S
    · by_cases hc : ∃ i : PairIndex M S f, c = i.high ∨ c = i.low
      · obtain ⟨i, hc⟩ := hc
        by_cases hi : expensiveCount M f i.low i.low + 1 = q
        · rw [bundleCost_eq_size, (houtside v hvS hvn i c hc).1 hi]
          have ht := threshold_le_balanced M hr hs v
          have hsz : (q : ℝ) ≤ (bundle g c).card := by exact_mod_cast hmin c
          nlinarith only [ht, hsz, hr]
        · have he := (houtside v hvS hvn i c hc).2 hi
          have hsz := (hordinary i hi).size c hc
          rw [cost_eq_of_counts M r hsz he]
          apply separated_comparison M hr (hf.energyMinimum M) hs hvc
          intro _ _ hbad
          obtain ⟨j, hj, _⟩ := PairIndex.of_bad hvS
            (hc.elim (fun h => h ▸ i.members.1) (fun h => h ▸ i.members.2)) hbad
          exact (hvn j).1 hj.symm
      · have hcn : ∀ i : PairIndex M S f, c ≠ i.high ∧ c ≠ i.low :=
          fun i => ⟨fun h => hc ⟨i, Or.inl h⟩, fun h => hc ⟨i, Or.inr h⟩⟩
        rw [hother c hcn]
        apply separated_comparison M hr (hf.energyMinimum M) hs hvc
        intro _ hcS hbad
        obtain ⟨i, hi, _⟩ := PairIndex.of_bad hvS hcS hbad
        exact (hvn i).1 hi.symm
    · have ht := separated_outside_threshold M hf.1.1 r hs hvS
      have hsz : (q : ℝ) ≤ (bundle g c).card := by exact_mod_cast hmin c
      exact ht.trans (hsz.trans (cost_ge_size M hr1 g v c))

end ResearchMain.Chores
