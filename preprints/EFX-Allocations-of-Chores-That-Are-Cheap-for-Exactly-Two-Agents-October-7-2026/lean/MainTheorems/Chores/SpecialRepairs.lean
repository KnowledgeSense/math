import MainTheorems.Chores.BadPairs
import MainTheorems.Chores.ParallelTransfer
import MainTheorems.Chores.SpecialPair

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

theorem all_special_pairs (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hL : ∀ i : PairIndex M S f, expensiveCount M f i.low i.low + 1 = q) :
    ∃ g : E → A, EFX M r g := by
  classical
  let P : PairedTransfers A E (PairIndex M S f) :=
    { source := PairIndex.high
      target := PairIndex.low
      chore := fun i => Classical.choose i.bad.2.1
      source_injective := PairIndex.high_injective M hf hs
      target_injective := PairIndex.low_injective M hf hs
      cross := PairIndex.high_ne_low M hf hs }
  have he (i : PairIndex M S f) : P.chore i ∈ bundle f i.high ∧ M.Cheap i.high (P.chore i) :=
    Classical.choose_spec i.bad.2.1
  have howner (i : PairIndex M S f) : f (P.chore i) = P.source i :=
    (mem_bundle f i.high (P.chore i)).mp (he i).1
  have hcheapLow (i : PairIndex M S f) : M.Cheap i.low (P.chore i) :=
    optimal_bad_source_pure M hf hs i.members.1 i.members.2 i.bad (P.chore i) (he i).1 (he i).2
  let g := P.allocation f
  have hsep : Separated M S g :=
    P.separated M hf.1.1 (fun i => i.members.2) hcheapLow
  have hsource (i : PairIndex M S f) :
      bundle g i.high = (bundle f i.high).erase (P.chore i) := P.source_bundle howner i
  have htarget (i : PairIndex M S f) :
      bundle g i.low = insert (P.chore i) (bundle f i.low) := P.target_bundle howner i
  have hother {c : A} (hc : ∀ i : PairIndex M S f, c ≠ i.high ∧ c ≠ i.low) :
      bundle g c = bundle f c := P.other_bundle howner hc
  have hdata (i : PairIndex M S f) :
      (bundle g i.high).card = q ∧ (bundle g i.low).card = q + 2 ∧
      expensiveCount M g i.high i.high = q ∧
      expensiveCount M g i.low i.low = expensiveCount M f i.low i.low ∧
      cheapCount M g i.high i.high = 0 ∧ cheapCount M g i.low i.low = 3 := by
    obtain ⟨hsa, hsb, _, _⟩ := optimal_special_pair M hf hs i.members.1 i.members.2 i.bad (hL i)
    have hn : P.chore i ∉ bundle f i.low := by
      intro h
      exact i.bad.1 ((mem_bundle f i.high (P.chore i)).mp (he i).1 |>.symm.trans
        ((mem_bundle f i.low (P.chore i)).mp h))
    have ha : (bundle g i.high).card = q := by
      rw [hsource, Finset.card_erase_of_mem (he i).1, hsa]
      omega
    have hb : (bundle g i.low).card = q + 2 := by
      rw [htarget, Finset.card_insert_of_notMem hn, hsb]
    have hea : expensiveCount M g i.high i.high = q := by
      rw [expensiveCount, hsource, Finset.filter_erase]
      have hncheap : P.chore i ∉ (bundle f i.high).filter (fun e => ¬M.Cheap i.high e) := by
        simp [(he i).2]
      rw [Finset.erase_eq_of_notMem hncheap]
      exact (minimum_bad_counts M (hf.energyMinimum M) hs i.members.1 i.members.2 i.bad).1.trans (hL i)
    have heb : expensiveCount M g i.low i.low = expensiveCount M f i.low i.low := by
      simp [expensiveCount, htarget, Finset.filter_insert, hcheapLow i]
    have hca := cheap_add_expensive M g i.high i.high
    have hcb := cheap_add_expensive M g i.low i.low
    rw [ha, hea] at hca
    rw [hb, heb] at hcb
    exact ⟨ha, hb, hea, heb, by omega, by have := hL i; omega⟩
  have hown (i : PairIndex M S f) : OwnCheap M g i.low := by
    rw [ownCheap_iff_count, (hdata i).2.2.2.2.2]
    omega
  have hpHigh (i : PairIndex M S f) : Pure M g i.high i.low := by
    intro e he hc
    have h := (ownCheap_iff_count M g i.high).mp ⟨e, he, hc⟩
    rw [(hdata i).2.2.2.2.1] at h
    omega
  have hpLow (i : PairIndex M S f) : Pure M g i.low i.high := by
    intro e he' hc
    rw [htarget] at he'
    rcases Finset.mem_insert.mp he' with h | h
    · subst e
      exact (he i).2
    · exact minimum_bad_target_pure M (hf.energyMinimum M) hs i.members.1 i.members.2
        i.bad e h hc
  have hthHigh (i : PairIndex M S f) : threshold M r g i.high = r * ((q : ℝ) - 1) := by
    have hq : 0 < q := by have := hL i; omega
    rw [threshold_eq_counts M r g i.high (by rw [← Finset.card_pos, (hdata i).1]; exact hq),
      (hdata i).2.2.2.2.1, ite_eq_right (Nat.lt_irrefl 0), (hdata i).1]
  have hthLow (i : PairIndex M S f) :
      threshold M r g i.low = 2 + r * expensiveCount M f i.low i.low := by
    rw [positive_threshold M r (hown i), (hdata i).2.1, (hdata i).2.2.2.1]
    have h := hL i
    have h' : (expensiveCount M f i.low i.low : ℝ) + 1 = q := by exact_mod_cast h
    push_cast
    nlinarith
  have hth (i : PairIndex M S f) {v : A} (hv : v = i.high ∨ v = i.low) :
      threshold M r g v ≤ r * q := by
    have h' : (expensiveCount M f i.low i.low : ℝ) + 1 = q := by exact_mod_cast hL i
    rcases hv with rfl | rfl
    · rw [hthHigh]
      nlinarith
    · rw [hthLow]
      nlinarith
  have hmin (c : A) : q ≤ (bundle g c).card := by
    by_cases hc : ∃ i : PairIndex M S f, c = i.high ∨ c = i.low
    · obtain ⟨i, rfl | rfl⟩ := hc
      · rw [(hdata i).1]
      · rw [(hdata i).2.1]
        omega
    · have hc' : ∀ i : PairIndex M S f, c ≠ i.high ∧ c ≠ i.low := by
        intro i
        exact ⟨fun h => hc ⟨i, Or.inl h⟩, fun h => hc ⟨i, Or.inr h⟩⟩
      rw [hother hc']
      exact (hs c).1
  have hwhole {c v : A} (hv : v ∈ S)
      (hc : ∃ i : PairIndex M S f, c = i.high ∨ c = i.low)
      (hn : ∀ i : PairIndex M S f, v ≠ i.high ∧ v ≠ i.low) :
      expensiveCount M g v c = (bundle g c).card := by
    obtain ⟨i, rfl | rfl⟩ := hc
    · exact pure_outside_expensive M hsep i.bad.1 (hpHigh i) hv (hn i).1 (hn i).2
    · exact pure_outside_expensive M hsep i.bad.1.symm (hpLow i) hv (hn i).2 (hn i).1
  refine ⟨g, ?_⟩
  rw [efx_iff_threshold M hr]
  intro v c hvc
  by_cases hv : ∃ i : PairIndex M S f, v = i.high ∨ v = i.low
  · obtain ⟨i, hv⟩ := hv
    have hvS : v ∈ S := hv.elim (fun h => h ▸ i.members.1) (fun h => h ▸ i.members.2)
    by_cases hc : c = i.high ∨ c = i.low
    · rcases hv with rfl | rfl <;> rcases hc with rfl | rfl
      · exact False.elim (hvc rfl)
      · rw [hthHigh, bundleCost_eq_size, pure_observer_expensive M hsep i.members.1 (hpLow i),
          (hdata i).2.1, (hdata i).2.2.2.1]
        have h' : (expensiveCount M f i.low i.low : ℝ) + 1 = q := by exact_mod_cast hL i
        push_cast
        nlinarith
      · rw [hthLow, bundleCost_eq_size, pure_observer_expensive M hsep i.members.2 (hpHigh i),
          (hdata i).1, (hdata i).2.2.1]
        have h' : (expensiveCount M f i.low i.low : ℝ) + 1 = q := by exact_mod_cast hL i
        nlinarith
      · exact False.elim (hvc rfl)
    · have hca : c ≠ i.high := fun h => hc (Or.inl h)
      have hcb : c ≠ i.low := fun h => hc (Or.inr h)
      by_cases hcp : ∃ j : PairIndex M S f, c = j.high ∨ c = j.low
      · obtain ⟨j, hj⟩ := hcp
        have hij : i ≠ j := by
          intro h
          subst j
          exact hc hj
        have hvh : v ≠ j.high := fun h => hij (PairIndex.endpoint_unique M hf hs hv (Or.inl h))
        have hvl : v ≠ j.low := fun h => hij (PairIndex.endpoint_unique M hf hs hv (Or.inr h))
        have hewhole : expensiveCount M g v c = (bundle g c).card := by
          rcases hj with rfl | rfl
          · exact pure_outside_expensive M hsep j.bad.1 (hpHigh j) hvS hvh hvl
          · exact pure_outside_expensive M hsep j.bad.1.symm (hpLow j) hvS hvl hvh
        rw [bundleCost_eq_size, hewhole]
        have ht := hth i hv
        have hc' : (q : ℝ) ≤ (bundle g c).card := by exact_mod_cast hmin c
        nlinarith
      · have hc' : ∀ j : PairIndex M S f, c ≠ j.high ∧ c ≠ j.low := by
          intro j
          exact ⟨fun h => hcp ⟨j, Or.inl h⟩, fun h => hcp ⟨j, Or.inr h⟩⟩
        rw [hother hc', bundleCost_eq_size]
        have hE : q ≤ expensiveCount M f v c := by
          by_cases hcS : c ∈ S
          · rcases hv with rfl | rfl
            · simpa only [hL i] using optimal_pair_high_margin M hf hs i.members.1 i.members.2 hcS i.bad hca hcb
            · simpa only [hL i] using optimal_pair_low_margin M hf hs i.members.1 i.members.2 hcS i.bad hca hcb
          · rw [separated_outside_target_expensive M hf.1.1 hvS hcS]
            exact (hs c).1
        have he' : (q : ℝ) ≤ expensiveCount M f v c := by exact_mod_cast hE
        have hcsize : (q : ℝ) ≤ (bundle f c).card := by exact_mod_cast (hs c).1
        have ht := hth i hv
        nlinarith
  · have hv' : ∀ i : PairIndex M S f, v ≠ i.high ∧ v ≠ i.low := by
      intro i
      exact ⟨fun h => hv ⟨i, Or.inl h⟩, fun h => hv ⟨i, Or.inr h⟩⟩
    have ht : threshold M r g v = threshold M r f v := by
      apply threshold_eq_of_counts M r
      · rw [hother hv']
      · rw [expensiveCount, hother hv']
        rfl
    rw [ht]
    by_cases hvS : v ∈ S
    · by_cases hc : ∃ i : PairIndex M S f, c = i.high ∨ c = i.low
      · rw [bundleCost_eq_size, hwhole hvS hc hv']
        have ht' := threshold_le_balanced M hr hs v
        have hc' : (q : ℝ) ≤ (bundle g c).card := by exact_mod_cast hmin c
        nlinarith
      · have hc' : ∀ i : PairIndex M S f, c ≠ i.high ∧ c ≠ i.low := by
          intro i
          exact ⟨fun h => hc ⟨i, Or.inl h⟩, fun h => hc ⟨i, Or.inr h⟩⟩
        rw [hother hc']
        apply separated_comparison M hr (hf.energyMinimum M) hs hvc
        intro hvS' hcS hbad
        obtain ⟨i, hi, _⟩ := PairIndex.of_bad hvS' hcS hbad
        exact (hv' i).1 hi.symm
    · have ht' := separated_outside_threshold M hf.1.1 r hs hvS
      have hc' := cost_ge_size M (show 1 ≤ r by linarith) g v c
      have hcsize : (q : ℝ) ≤ (bundle g c).card := by exact_mod_cast hmin c
      linarith

end ResearchMain.Chores
