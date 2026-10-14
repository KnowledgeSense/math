import MainTheorems.Chores.LongDonorTransfer
import MainTheorems.Chores.PairCosts

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace LongDonorTransfer

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ f : E → A} {a b k : A} {q : ℕ}

theorem long_donor_efx (T : LongDonorTransfer M S f a b k)
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hunique : UniqueBad M S f a b) (hL : expensiveCount M f b b + 2 = q)
    (hsizeK : (bundle f k).card = q + 1) (hcheapK : cheapCount M f k k = 2)
    (hpK : Pure M f k a) {r : ℝ} (hr : 2 < r) : EFX M r T.allocation := by
  let g := T.allocation
  have ha := T.donor.source_mem
  have hb := T.low_mem
  have hk := T.donor.target_mem
  have hab := T.high_ne_low
  have hak := T.donor.distinct
  have hkb := T.donor_ne_low
  have hpA := optimal_bad_source_pure M hf hs ha hb hunique.1
  have hpB := minimum_bad_target_pure M (hf.energyMinimum M) hs ha hb hunique.1
  have hcounts := (minimum_bad_counts M (hf.energyMinimum M) hs ha hb hunique.1).1
  have hcountsR : (expensiveCount M f a a : ℝ) = expensiveCount M f b b + 1 := by exact_mod_cast hcounts
  have hLR : (expensiveCount M f b b : ℝ) + 2 = q := by exact_mod_cast hL
  have hEk : expensiveCount M f k k + 1 = q := by
    have ht := cheap_add_expensive M f k k
    rw [hcheapK, hsizeK] at ht
    omega
  have hEkR : (expensiveCount M f k k : ℝ) + 1 = q := by exact_mod_cast hEk
  have hsizeAR : (q : ℝ) ≤ (bundle f a).card ∧ ((bundle f a).card : ℝ) ≤ q + 1 := by
    exact ⟨by exact_mod_cast (hs a).1, by exact_mod_cast (hs a).2⟩
  have hsizeBR : (q : ℝ) ≤ (bundle f b).card ∧ ((bundle f b).card : ℝ) ≤ q + 1 := by
    exact ⟨by exact_mod_cast (hs b).1, by exact_mod_cast (hs b).2⟩
  have hcFill {v : A} (hv : v ∈ S) : itemCost M r v T.donor.firstChore = r := by
    rw [itemCost, ite_eq_right (filler_not_cheap M hv T.donor.filler)]
  have hcDA : itemCost M r a T.donor.secondChore = 1 := by
    rw [itemCost, ite_eq_left T.donor.sourceCheap]
  have hcDK : itemCost M r k T.donor.secondChore = 1 := by
    rw [itemCost, ite_eq_left T.donor.targetCheap]
  have hcDB : itemCost M r b T.donor.secondChore = r := by
    rw [itemCost, ite_eq_right (two_cheap_third M hak T.donor.sourceCheap T.donor.targetCheap hab.symm hkb.symm)]
  have hcCA : itemCost M r a T.pairChore = 1 := by rw [itemCost, ite_eq_left T.highCheap]
  have hcCB : itemCost M r b T.pairChore = 1 := by rw [itemCost, ite_eq_left T.lowCheap]
  have hcCK : itemCost M r k T.pairChore = r := by
    rw [itemCost, ite_eq_right (two_cheap_third M hab T.highCheap T.lowCheap hak.symm hkb)]
  have hownA : OwnCheap M g a := by
    refine ⟨T.pairChore, ?_, T.highCheap⟩
    apply (mem_bundle g a _).mpr
    exact (exchange_right T.intermediate T.donor.firstChore T.pairChore).trans T.first_owner
  have hownB : OwnCheap M g b := by
    have htwo := optimal_bad_target_two_cheap M hf hs ha hb hunique.1
    have hc : T.pairChore ∈ (bundle f b).filter (M.Cheap b) :=
      Finset.mem_filter.mpr ⟨(mem_bundle f b _).mpr T.pairOwner, T.lowCheap⟩
    have hcard := Finset.card_erase_add_one hc
    have hcheap : cheapCount M g b b + 1 = cheapCount M f b b := by
      rw [cheapCount, T.low_bundle, Finset.filter_insert,
        ite_eq_right (filler_not_cheap M hb T.donor.filler), Finset.filter_erase]
      exact hcard
    rw [ownCheap_iff_count]
    omega
  have hownK : OwnCheap M g k := by
    have hc : T.donor.secondChore ∈ (bundle f k).filter (M.Cheap k) :=
      Finset.mem_filter.mpr ⟨(mem_bundle f k _).mpr T.donor.secondOwner, T.donor.targetCheap⟩
    have hcard := Finset.card_erase_add_one hc
    have hcheap : cheapCount M g k k + 1 = cheapCount M f k k := by
      rw [cheapCount, T.donor_bundle, Finset.filter_erase]
      exact hcard
    rw [ownCheap_iff_count]
    omega
  have hownKold : OwnCheap M f k := by rw [ownCheap_iff_count, hcheapK]; omega
  have hcostA : bundleCost M r a (bundle f a) =
      r * ((q : ℝ) - 1) + (bundle f a).card - q + 1 := by
    rw [bundleCost_eq_size]
    have hE : (expensiveCount M f a a : ℝ) = q - 1 := by linarith only [hcountsR, hLR]
    rw [hE]
    ring
  have hcostB : bundleCost M r b (bundle f b) =
      r * ((q : ℝ) - 2) + (bundle f b).card - q + 2 := by
    rw [bundleCost_eq_size]
    have hE : (expensiveCount M f b b : ℝ) = q - 2 := by linarith only [hLR]
    rw [hE]
    ring
  have hcostK : bundleCost M r k (bundle f k) = 2 + r * ((q : ℝ) - 1) := by
    rw [bundleCost_eq_size, hsizeK]
    push_cast
    have hE : (expensiveCount M f k k : ℝ) = q - 1 := by linarith only [hEkR]
    rw [hE]
    ring
  have htA : threshold M r g a = r * ((q : ℝ) - 2) + (bundle f a).card - q + 2 := by
    rw [positive_threshold_cost M r hownA]
    have ht := T.high_cost r a
    rw [hcFill ha, hcDA, hcCA, hcostA] at ht
    change bundleCost M r a (bundle g a) + r =
      r * ((q : ℝ) - 1) + (bundle f a).card - q + 1 + 1 + 1 at ht
    linarith only [ht]
  have htB : threshold M r g b = r * ((q : ℝ) - 1) + (bundle f b).card - q := by
    rw [positive_threshold_cost M r hownB]
    have ht := T.low_cost r b
    rw [hcFill hb, hcCB, hcostB] at ht
    change bundleCost M r b (bundle g b) + 1 =
      r * ((q : ℝ) - 2) + (bundle f b).card - q + 2 + r at ht
    linarith only [ht]
  have htK : threshold M r g k = r * ((q : ℝ) - 1) := by
    rw [positive_threshold_cost M r hownK]
    have ht := T.donor_cost r k
    rw [hcDK, hcostK] at ht
    change bundleCost M r k (bundle g k) + 1 = 2 + r * ((q : ℝ) - 1) at ht
    linarith only [ht]
  have hmin (c : A) : q ≤ (bundle g c).card := by
    by_cases hca : c = a
    · subst c
      rw [T.high_card]
      have ht := (hs a).1
      omega
    · by_cases hcb : c = b
      · subst c
        rw [T.low_card]
        exact (hs b).1
      · by_cases hck : c = k
        · subst c
          have ht := T.donor_card
          change (bundle g k).card + 1 = (bundle f k).card at ht
          omega
        · rw [T.other_bundle hca hcb hck]
          exact (hs c).1
  have htriple {v c : A} (hv : v = a ∨ v = b ∨ v = k)
      (hc : c = a ∨ c = b ∨ c = k) (hvc : v ≠ c) :
      threshold M r g v ≤ bundleCost M r v (bundle g c) := by
    rcases hv with hv | hv | hv <;> rcases hc with hc | hc | hc <;> subst v <;> subst c
    · exact False.elim (hvc rfl)
    · rw [htA]
      have ht := T.low_cost r a
      rw [hcCA, hcFill ha, pure_observer_cost M hf.1.1 ha hpB r, hcostB] at ht
      change bundleCost M r a (bundle g b) + 1 =
        r * ((q : ℝ) - 2) + (bundle f b).card - q + 2 + r at ht
      nlinarith only [ht, hsizeAR.2, hsizeBR.1, hr]
    · rw [htA]
      have ht := T.donor_cost r a
      rw [hcDA, pure_observer_cost M hf.1.1 ha hpK r, hcostK] at ht
      change bundleCost M r a (bundle g k) + 1 = 2 + r * ((q : ℝ) - 1) at ht
      nlinarith only [ht, hsizeAR.2, hr]
    · rw [htB]
      have ht := T.high_cost r b
      rw [hcFill hb, hcDB, hcCB, pure_observer_cost M hf.1.1 hb hpA r, hcostA] at ht
      change bundleCost M r b (bundle g a) + r =
        r * ((q : ℝ) - 1) + (bundle f a).card - q + 1 + r + 1 at ht
      nlinarith only [ht, hsizeBR.2, hsizeAR.1]
    · exact False.elim (hvc rfl)
    · rw [htB]
      have ht := T.donor_cost r b
      rw [hcDB, pure_outside_cost M hf.1.1 hak.symm hpK hb hkb.symm hab.symm r, hsizeK] at ht
      push_cast at ht
      change bundleCost M r b (bundle g k) + r = r * ((q : ℝ) + 1) at ht
      nlinarith only [ht, hsizeBR.2, hr]
    · rw [htK]
      have ht := T.high_cost r k
      rw [hcFill hk, hcDK, hcCK, pure_outside_cost M hf.1.1 hab hpA hk hak.symm hkb r] at ht
      change bundleCost M r k (bundle g a) + r = r * (bundle f a).card + 1 + r at ht
      nlinarith only [ht, hsizeAR.1, hr]
    · rw [htK]
      have ht := T.low_cost r k
      rw [hcCK, hcFill hk, pure_outside_cost M hf.1.1 hab.symm hpB hk hkb hak.symm r] at ht
      change bundleCost M r k (bundle g b) + r = r * (bundle f b).card + r at ht
      nlinarith only [ht, hsizeBR.1, hr]
    · exact False.elim (hvc rfl)
  have hr1 : 1 ≤ r := by linarith
  rw [efx_iff_threshold M hr]
  intro v c hvc
  by_cases hv : v = a ∨ v = b ∨ v = k
  · by_cases hc : c = a ∨ c = b ∨ c = k
    · exact htriple hv hc hvc
    · have hca : c ≠ a := fun ht => hc (Or.inl ht)
      have hcb : c ≠ b := fun ht => hc (Or.inr (Or.inl ht))
      have hck : c ≠ k := fun ht => hc (Or.inr (Or.inr ht))
      rw [T.other_bundle hca hcb hck]
      rcases hv with hv | hv | hv <;> subst v
      · rw [htA]
        have hbound : r * ((q : ℝ) - 1) + 1 ≤ bundleCost M r a (bundle f c) := by
          rw [bundleCost_eq_size]
          have hsz : (q : ℝ) ≤ (bundle f c).card := by exact_mod_cast (hs c).1
          have hE : q ≤ expensiveCount M f a c + 1 := by
            by_cases hcS : c ∈ S
            · have ht := optimal_pair_high_margin M hf hs ha hb hcS hunique.1 hca hcb
              omega
            · rw [separated_outside_target_expensive M hf.1.1 ha hcS]
              have ht := (hs c).1
              omega
          have hE' : (q : ℝ) ≤ expensiveCount M f a c + 1 := by exact_mod_cast hE
          nlinarith only [hsz, hE', hr]
        nlinarith only [hbound, hsizeAR.2, hr]
      · rw [htB]
        have hbound : r * ((q : ℝ) - 1) + 1 ≤ bundleCost M r b (bundle f c) := by
          rw [bundleCost_eq_size]
          have hsz : (q : ℝ) ≤ (bundle f c).card := by exact_mod_cast (hs c).1
          have hE : q ≤ expensiveCount M f b c + 1 := by
            by_cases hcS : c ∈ S
            · have ht := optimal_pair_low_margin M hf hs ha hb hcS hunique.1 hca hcb
              omega
            · rw [separated_outside_target_expensive M hf.1.1 hb hcS]
              have ht := (hs c).1
              omega
          have hE' : (q : ℝ) ≤ expensiveCount M f b c + 1 := by exact_mod_cast hE
          nlinarith only [hsz, hE', hr]
        nlinarith only [hbound, hsizeBR.2]
      · rw [htK]
        have ht := separated_comparison M hr (hf.energyMinimum M) hs hvc
          (fun hk' hc' hbad => hak.symm (hunique.2 k hk' c hc' hbad).1)
        rw [positive_threshold_cost M r hownKold, hcostK] at ht
        linarith only [ht]
  · have hva : v ≠ a := fun ht => hv (Or.inl ht)
    have hvb : v ≠ b := fun ht => hv (Or.inr (Or.inl ht))
    have hvk : v ≠ k := fun ht => hv (Or.inr (Or.inr ht))
    have ht : threshold M r g v = threshold M r f v := by
      have hbun := T.other_bundle hva hvb hvk
      apply threshold_eq_of_counts M r
      · rw [hbun]
      · rw [expensiveCount, hbun]
        rfl
    rw [ht]
    by_cases hvS : v ∈ S
    · have hcD : itemCost M r v T.donor.secondChore = r := by
        rw [itemCost, ite_eq_right (two_cheap_third M hak T.donor.sourceCheap T.donor.targetCheap hva hvk)]
      have hcC : itemCost M r v T.pairChore = r := by
        rw [itemCost, ite_eq_right (two_cheap_third M hab T.highCheap T.lowCheap hva hvb)]
      by_cases hca : c = a
      · subst c
        have htCost := T.high_cost r v
        rw [hcFill hvS, hcD, hcC] at htCost
        have htOld := separated_comparison M hr (hf.energyMinimum M) hs hvc
          (fun hvS' ha' hbad => hva (hunique.2 v hvS' a ha' hbad).1)
        change bundleCost M r v (bundle g a) + r = bundleCost M r v (bundle f a) + r + r at htCost
        linarith only [htCost, htOld, hr]
      · by_cases hcb : c = b
        · subst c
          have htCost := T.low_cost r v
          rw [hcFill hvS, hcC] at htCost
          have htOld := separated_comparison M hr (hf.energyMinimum M) hs hvc
            (fun hvS' hb' hbad => hva (hunique.2 v hvS' b hb' hbad).1)
          change bundleCost M r v (bundle g b) + r = bundleCost M r v (bundle f b) + r at htCost
          linarith only [htCost, htOld]
        · by_cases hck : c = k
          · subst c
            have htCost := T.donor_cost r v
            rw [hcD, pure_outside_cost M hf.1.1 hak.symm hpK hvS hvk hva r, hsizeK] at htCost
            have htOld := threshold_le_balanced M hr hs v
            push_cast at htCost
            change bundleCost M r v (bundle g k) + r = r * ((q : ℝ) + 1) at htCost
            linarith only [htCost, htOld]
          · rw [T.other_bundle hca hcb hck]
            exact separated_comparison M hr (hf.energyMinimum M) hs hvc
              (fun hvS' hc' hbad => hva (hunique.2 v hvS' c hc' hbad).1)
    · have htOld := separated_outside_threshold M hf.1.1 r hs hvS
      have hcost := cost_ge_size M hr1 g v c
      have hsz : (q : ℝ) ≤ (bundle g c).card := by exact_mod_cast hmin c
      linarith only [htOld, hcost, hsz]

end LongDonorTransfer

end ResearchMain.Chores
