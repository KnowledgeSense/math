import MainTheorems.Chores.EqualCounts
import MainTheorems.Chores.PairReversal

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

structure TokenReady (M : TwoCheapModel A E) (S : Finset A) (f₀ : E → A) (q : ℕ) (k : A) where
  allocation : E → A
  high : A
  low : A
  optimal : Optimal M S f₀ allocation
  size : ∀ v, q ≤ (bundle allocation v).card ∧ (bundle allocation v).card ≤ q + 1
  high_mem : high ∈ S
  low_mem : low ∈ S
  donor_mem : k ∈ S
  unique_bad : UniqueBad M S allocation high low
  low_bound : expensiveCount M allocation low low + 3 ≤ q
  donor_high : k ≠ high
  donor_low : k ≠ low
  donor_count : expensiveCount M allocation k k = expensiveCount M allocation low low + 1
  donor_pure : Pure M allocation k high
  high_observer : expensiveCount M allocation high k = expensiveCount M allocation low low + 1
  donor_cheap : 2 ≤ cheapCount M allocation k k

theorem tight_token_donor (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ v, q ≤ (bundle f v).card ∧ (bundle f v).card ≤ q + 1)
    {a b k : A} (ha : a ∈ S) (hb : b ∈ S) (hkS : k ∈ S)
    (hunique : UniqueBad M S f a b) (hka : k ≠ a) (hkb : k ≠ b)
    (hL : expensiveCount M f b b + 3 ≤ q)
    (htight : expensiveCount M f a k = expensiveCount M f b b + 1) :
    (∃ g : E → A, EFX M r g) ∨
      (expensiveCount M f k k = expensiveCount M f b b + 1 ∧
        Pure M f k a ∧ 2 ≤ cheapCount M f k k) := by
  have hcounts := (minimum_bad_counts M (hf.energyMinimum M) hs ha hb hunique.1).1
  have hsum := cheap_add_expensive M f a k
  have hpos : 0 < cheapCount M f a k := by
    have hsz := (hs k).1
    omega
  obtain ⟨d, hd'⟩ := Finset.card_pos.mp hpos
  obtain ⟨hd, hda⟩ := Finset.mem_filter.mp hd'
  have hlower := minimum_exchange_bound M (hf.energyMinimum M) ha hkS hka.symm hd hda
  have hupper := separated_observer_expensive_ge M hf.1.1 ha (b := k)
  by_cases hk : expensiveCount M f k k = expensiveCount M f b b
  · exact Or.inl (neutral_handoff M hr hf hs ha hb hkS hunique hka hkb hk (by omega) hd hda)
  · have hcountK : expensiveCount M f k k = expensiveCount M f b b + 1 := by omega
    have hEq : expensiveCount M f a k = expensiveCount M f k k := by omega
    have hpK := pure_of_equal_expensive M hf.1.1 ha hEq
    have hsumK := cheap_add_expensive M f k k
    have hsizeK := (hs k).1
    exact Or.inr ⟨hcountK, hpK, by omega⟩

theorem prepare_token_pair (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ v, q ≤ (bundle f v).card ∧ (bundle f v).card ≤ q + 1)
    {a b k : A} (ha : a ∈ S) (hb : b ∈ S) (hkS : k ∈ S)
    (hunique : UniqueBad M S f a b) (hka : k ≠ a) (hkb : k ≠ b)
    (hL : expensiveCount M f b b + 3 ≤ q) (hkpos : 0 < expensiveCount M f k k) :
    (∃ g : E → A, EFX M r g) ∨ Nonempty (TokenReady M S f₀ q k) := by
  by_cases hmarginA : expensiveCount M f b b + 2 ≤ expensiveCount M f a k
  · by_cases hmarginB : expensiveCount M f b b + 2 ≤ expensiveCount M f b k
    · exact Or.inl (direct_buffer M hr hf hs ha hb hkS hunique hka hkb (by omega) hkpos hmarginA hmarginB)
    · have hmargin := optimal_pair_low_margin M hf hs ha hb hkS hunique.1 hka hkb
      have htight : expensiveCount M f b k = expensiveCount M f b b + 1 := by omega
      obtain ⟨B⟩ := exists_basic_exchange M hf.1.1 hs ha hb hunique.1
      obtain ⟨hunique', hf', hEa⟩ := B.reverse_unique_pair hf hs hunique
      have hL' : expensiveCount M B.allocation a a + 3 ≤ q := by rwa [hEa]
      have htight' : expensiveCount M B.allocation b k = expensiveCount M B.allocation a a + 1 := by
        rw [B.other_expensive b hka hkb, hEa, htight]
      rcases tight_token_donor M hr hf' (B.balanced hs) hb ha hkS hunique' hkb hka hL' htight' with hefx | hready
      · exact Or.inl hefx
      · exact Or.inr ⟨⟨B.allocation, b, a, hf', B.balanced hs, hb, ha, hkS, hunique', hL', hkb, hka,
          hready.1, hready.2.1, htight', hready.2.2⟩⟩
  · have hmargin := optimal_pair_high_margin M hf hs ha hb hkS hunique.1 hka hkb
    have htight : expensiveCount M f a k = expensiveCount M f b b + 1 := by omega
    rcases tight_token_donor M hr hf hs ha hb hkS hunique hka hkb hL htight with hefx | hready
    · exact Or.inl hefx
    · exact Or.inr ⟨⟨f, a, b, hf, hs, ha, hb, hkS, hunique, hL, hka, hkb,
        hready.1, hready.2.1, htight, hready.2.2⟩⟩

end ResearchMain.Chores
