import MainTheorems.Chores.EqualCounts
import MainTheorems.Chores.LongDonor

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

theorem boundary_tight_high (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b k : A} (ha : a ∈ S) (hb : b ∈ S) (hkS : k ∈ S)
    (hunique : UniqueBad M S f a b) (hka : k ≠ a) (hkb : k ≠ b)
    (hL : expensiveCount M f b b + 2 = q)
    (htight : expensiveCount M f a k + 1 = q) : ∃ g : E → A, EFX M r g := by
  have hcounts := (minimum_bad_counts M (hf.energyMinimum M) hs ha hb hunique.1).1
  have hsum := cheap_add_expensive M f a k
  have hpos : 0 < cheapCount M f a k := by
    have ht := (hs k).1
    omega
  obtain ⟨d, hd'⟩ := Finset.card_pos.mp hpos
  obtain ⟨hd, hda⟩ := Finset.mem_filter.mp hd'
  have heq := (mem_bundle f k d).mp hd
  have hdk : M.Cheap k d := by
    simpa only [heq] using separated_owner_cheap M hf.1.1 ha hda
  have hlower := minimum_exchange_bound M (hf.energyMinimum M) ha hkS hka.symm hd hda
  have hupper := separated_observer_expensive_ge M hf.1.1 ha (b := k)
  by_cases hk : expensiveCount M f k k = expensiveCount M f b b
  · exact neutral_handoff M hr hf hs ha hb hkS hunique hka hkb hk (by omega) hd hda
  · have hcountK : expensiveCount M f k k = expensiveCount M f a k := by omega
    have hpK := pure_of_equal_expensive M hf.1.1 ha hcountK.symm
    obtain ⟨e, he, hen⟩ := own_expensive_exists M (bad_expensive_positive M hunique.1)
    have hea := (mem_bundle f a e).mp he
    let B : ExchangeData M S f a k :=
      { firstChore := e
        secondChore := d
        firstOwner := hea
        secondOwner := heq
        source_mem := ha
        target_mem := hkS
        distinct := hka.symm
        filler := separated_expensive_filler M hf.1.1 (by simpa only [hea] using hen)
        sourceCheap := hda
        targetCheap := hdk }
    have hsumK := cheap_add_expensive M f k k
    by_cases hsizeK : (bundle f k).card = q
    · have hcheapK : cheapCount M f k k = 1 := by omega
      exact ⟨B.allocation, B.short_donor_efx hf hs hb hunique hkb hL hsizeK hcheapK hpK hr⟩
    · have hsizeK' : (bundle f k).card = q + 1 := by
        have ht := hs k
        omega
      have hcheapK : cheapCount M f k k = 2 := by omega
      obtain ⟨c, hc, hcb⟩ := bad_target_ownCheap M hf.1.1 hs ha hunique.1
      have hca := minimum_bad_target_pure M (hf.energyMinimum M) hs ha hb hunique.1 c hc hcb
      let T : LongDonorTransfer M S f a b k :=
        { donor := B
          pairChore := c
          pairOwner := (mem_bundle f b c).mp hc
          highCheap := hca
          lowCheap := hcb
          high_ne_low := hunique.1.1
          donor_ne_low := hkb
          low_mem := hb }
      exact ⟨T.allocation, T.long_donor_efx hf hs hunique hL hsizeK' hcheapK hpK hr⟩

theorem boundary_donor (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b k : A} (ha : a ∈ S) (hb : b ∈ S) (hkS : k ∈ S)
    (hunique : UniqueBad M S f a b) (hka : k ≠ a) (hkb : k ≠ b)
    (hL : expensiveCount M f b b + 2 = q) (hkpos : 0 < expensiveCount M f k k) :
    ∃ g : E → A, EFX M r g := by
  by_cases hmarginA : q ≤ expensiveCount M f a k
  · by_cases hmarginB : q ≤ expensiveCount M f b k
    · exact direct_buffer M hr hf hs ha hb hkS hunique hka hkb (by omega) hkpos (by omega) (by omega)
    · have hmargin := optimal_pair_low_margin M hf hs ha hb hkS hunique.1 hka hkb
      have htight : expensiveCount M f b k + 1 = q := by omega
      obtain ⟨B⟩ := exists_basic_exchange M hf.1.1 hs ha hb hunique.1
      obtain ⟨hunique', hf', hEa⟩ := B.reverse_unique_pair hf hs hunique
      have hL' : expensiveCount M B.allocation a a + 2 = q := by rwa [hEa]
      have htight' : expensiveCount M B.allocation b k + 1 = q := by
        rwa [B.other_expensive b hka hkb]
      exact boundary_tight_high M hr hf' (B.balanced hs) hb ha hkS hunique' hkb hka hL' htight'
  · have hmargin := optimal_pair_high_margin M hf hs ha hb hkS hunique.1 hka hkb
    have htight : expensiveCount M f a k + 1 = q := by omega
    exact boundary_tight_high M hr hf hs ha hb hkS hunique hka hkb hL htight

end ResearchMain.Chores
