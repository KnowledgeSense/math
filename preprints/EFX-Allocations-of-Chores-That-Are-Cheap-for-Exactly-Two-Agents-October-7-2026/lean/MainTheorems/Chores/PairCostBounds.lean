import MainTheorems.Chores.AggregateSplit
import MainTheorems.Chores.PairCosts

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A]

theorem outside_expensive_ge_pair_cheap (M : TwoCheapModel A E) {a b c v : A}
    (hab : a ≠ b) (hiso : IsolatedPair M a b) {f : E → A}
    (hc : c = a ∨ c = b) (hva : v ≠ a) (hvb : v ≠ b) :
    cheapCount M f c c ≤ expensiveCount M f v c := by
  apply Finset.card_le_card
  intro e he
  obtain ⟨he, hcheap⟩ := Finset.mem_filter.mp he
  have hpair := hiso e (by rcases hc with hc | hc <;> subst c; exact Or.inl hcheap; exact Or.inr hcheap)
  exact Finset.mem_filter.mpr ⟨he, two_cheap_third M hab hpair.1 hpair.2 hva hvb⟩

theorem outside_cost_ge_pair_cheap (M : TwoCheapModel A E) {a b c v : A}
    (hab : a ≠ b) (hiso : IsolatedPair M a b) {f : E → A}
    (hc : c = a ∨ c = b) (hva : v ≠ a) (hvb : v ≠ b) {r : ℝ} (hr : 1 ≤ r) :
    ((bundle f c).card : ℝ) + (r - 1) * cheapCount M f c c ≤
      bundleCost M r v (bundle f c) := by
  rw [bundleCost_eq_size]
  have he : (cheapCount M f c c : ℝ) ≤ expensiveCount M f v c := by
    exact_mod_cast outside_expensive_ge_pair_cheap M hab hiso hc hva hvb
  nlinarith only [he, hr]

theorem own_cheap_threshold_bound (M : TwoCheapModel A E) {f : E → A} {a : A}
    (hc : OwnCheap M f a) {r : ℝ} (hr : 1 ≤ r) :
    threshold M r f a ≤ r * ((bundle f a).card - 1) := by
  rw [positive_threshold M r hc]
  have he := ownCheap_expensive_lt_size M hc
  have he' : (expensiveCount M f a a : ℝ) + 1 ≤ (bundle f a).card := by
    exact_mod_cast (show expensiveCount M f a a + 1 ≤ (bundle f a).card by omega)
  nlinarith only [he', hr]

theorem all_cheap_threshold_bound (M : TwoCheapModel A E) {f : E → A} {a : A} {q : ℕ}
    (hc : ∀ e ∈ bundle f a, M.Cheap a e) (hs : (bundle f a).card ≤ q + 1)
    (r : ℝ) : threshold M r f a ≤ q := by
  by_cases hne : (bundle f a).Nonempty
  · obtain ⟨e, he⟩ := hne
    have hown : OwnCheap M f a := ⟨e, he, hc e he⟩
    have hE : expensiveCount M f a a = 0 := by
      rw [expensiveCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he hn
      exact hn (hc e he)
    rw [positive_threshold M r hown, hE, Nat.cast_zero, mul_zero, add_zero]
    have hs' : ((bundle f a).card : ℝ) ≤ q + 1 := by exact_mod_cast hs
    linarith only [hs']
  · rw [threshold, ite_eq_right hne]
    positivity

end ResearchMain.Chores
