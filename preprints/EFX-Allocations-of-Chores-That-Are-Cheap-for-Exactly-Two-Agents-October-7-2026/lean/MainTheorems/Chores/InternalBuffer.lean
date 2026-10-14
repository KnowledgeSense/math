import MainTheorems.Chores.ForeignExchange
import MainTheorems.Chores.OneFiller

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace ForeignExchange

theorem internal_one_filler {M : TwoCheapModel A E} {S U : Finset A} {f : E → A} {a b k : A}
    (B : ForeignExchange M S f a b k) (N : TwoCheapModel A E) {f₀ : E → A} {q : ℕ}
    (hf : Optimal N U f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hq : 2 ≤ q) (hUS : U ⊆ S) (ha : a ∈ U) (hb : b ∈ U) (hk : k ∉ U)
    (hunique : UniqueBad N U f a b) (hzero : expensiveCount N f b b = 0)
    (hone : ∀ v ∈ U, expensiveCount N f v v ≤ 1)
    (heq : ∀ v ∈ U, ∀ c ∈ U, expensiveCount N f v c = expensiveCount M f v c)
    {r : ℝ} (hr : 2 < r) :
    (∀ v ∈ U, ∀ c ∈ U, v ≠ c →
      threshold M r B.allocation v ≤ bundleCost M r v (bundle B.allocation c)) ∧
      (∀ v ∈ U, expensiveCount M B.allocation v v ≤ 1 ∧ OwnCheap M B.allocation v) := by
  have hnotDonor {v : A} (hv : v ∈ U) : v ≠ k := by intro ht; subst v; exact hk hv
  have hcounts := minimum_bad_counts N (hf.energyMinimum N) hs ha hb hunique.1
  have hhigh : expensiveCount M f a a = 1 := by rw [← heq a ha a ha]; omega
  have hlow : expensiveCount M f b b = 0 := by rw [← heq b hb b hb, hzero]
  have hownN {v : A} (hv : v ∈ U) : OwnCheap N f v := by
    rw [ownCheap_iff_count]
    have hsum := cheap_add_expensive N f v v
    have hsz := (hs v).1
    have he := hone v hv
    omega
  have hold {v c : A} (hv : v ∈ U) (hc : c ∈ U) (hvc : v ≠ c) (hskip : v ≠ a ∨ c ≠ b) :
      expensiveCount M f v v ≤ expensiveCount M f v c := by
    rw [← heq v hv v hv, ← heq v hv c hc]
    by_contra hn
    have hbad : Bad N f v c := ⟨hvc, hownN hv, by omega⟩
    obtain ⟨hva, hcb⟩ := hunique.2 v hv c hc hbad
    rcases hskip with hskip | hskip
    · exact hskip hva
    · exact hskip hcb
  have hbound {v : A} (hv : v ∈ U) : expensiveCount M B.allocation v v ≤ 1 := by
    by_cases hvb : v = b
    · subst v
      rw [B.low_expensive, hlow]
    · rw [B.other_expensive v (hnotDonor hv) hvb, ← heq v hv v hv]
      exact hone v hv
  have hcheap {v : A} (hv : v ∈ U) : OwnCheap M B.allocation v := by
    rw [ownCheap_iff_count]
    have hsum := cheap_add_expensive M B.allocation v v
    rw [B.card] at hsum
    have hsz := (hs v).1
    have he := hbound hv
    omega
  refine ⟨?_, fun v hv => ⟨hbound hv, hcheap hv⟩⟩
  intro v hv c hc hvc
  apply positive_comparison M (by linarith : 1 ≤ r) (hcheap hv)
  · rw [B.card, B.card]
    have hl := (hs c).1
    have hu := (hs v).2
    omega
  · by_cases hvb : v = b
    · subst v
      rw [B.low_expensive, hlow, zero_add]
      by_cases hca : c = a
      · subst c
        rw [B.other_expensive b B.donor_high.symm B.pair_distinct,
          ← heq b hb a ha,
          pure_observer_expensive N hf.1.1 hb
            (optimal_bad_source_pure N hf hs ha hb hunique.1)]
        omega
      · rw [B.other_expensive b (hnotDonor hc) hvc.symm, ← heq b hb c hc]
        have ht := optimal_pair_low_margin N hf hs ha hb hc hunique.1 hca hvc.symm
        omega
    · by_cases hva : v = a
      · subst v
        rw [B.high_expensive, hhigh]
        by_cases hcb : c = b
        · subst c
          have ht := B.target_count B.high_mem
          rw [ite_eq_left B.highCheap, ← heq a ha b hb] at ht
          omega
        · rw [B.other_expensive a (hnotDonor hc) hcb]
          have ht := hold ha hc hvc (Or.inr hcb)
          omega
      · rw [B.other_expensive v (hnotDonor hv) hvb,
          B.outsider_expensive (hUS hv) hva hvb c]
        exact hold hv hc hvc (Or.inl hva)

end ForeignExchange

end ResearchMain.Chores
