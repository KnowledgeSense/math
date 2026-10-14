import MainTheorems.Chores.RepairEFX
import MainTheorems.Chores.PairCostBounds

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

omit [DecidableEq E] in
theorem one_expensive_threshold (M : TwoCheapModel A E) {f : E → A} {v : A} {q : ℕ}
    {r : ℝ} (hr : 2 < r) (hc : OwnCheap M f v)
    (hs : (bundle f v).card ≤ q + 1) (he : expensiveCount M f v v ≤ 1) :
    threshold M r f v ≤ q + r - 1 := by
  rw [positive_threshold M r hc]
  have hs' : ((bundle f v).card : ℝ) ≤ q + 1 := by exact_mod_cast hs
  have he' : (expensiveCount M f v v : ℝ) ≤ 1 := by exact_mod_cast he
  nlinarith only [hs', he', hr]

theorem isolated_frame_efx (M : TwoCheapModel A E) {S : Finset A} {f g : E → A}
    {a b : A} {q : ℕ} {r : ℝ} (hr : 2 < r) (hq : 2 ≤ q)
    (hs : ∀ c, q ≤ (bundle g c).card ∧ (bundle g c).card ≤ q + 1)
    (hsf : ∀ c, (bundle f c).card ≤ q + 1)
    (B : OrdinaryStats M f g a b) (hL : expensiveCount M f b b + 2 ≤ q)
    (hU : ∀ v ∈ S \ {a, b}, expensiveCount M g v v ≤ 1 ∧ OwnCheap M g v)
    (hinternal : ∀ v ∈ S \ {a, b}, ∀ c ∈ S \ {a, b}, v ≠ c →
      threshold M r g v ≤ bundleCost M r v (bundle g c))
    (hpairToU : ∀ v c, (v = a ∨ v = b) → c ∈ S \ {a, b} →
      (bundle g c).card ≤ expensiveCount M g v c + 1)
    (hUToPair : ∀ v ∈ S \ {a, b}, ∀ c, (c = a ∨ c = b) →
      (bundle g c).card ≤ expensiveCount M g v c + 1)
    (hH : ∀ v, v ∉ S → ∀ e ∈ bundle g v, M.Cheap v e)
    (htoH : ∀ v ∈ S, ∀ c, c ∉ S → expensiveCount M g v c = (bundle g c).card) :
    EFX M r g := by
  have hr1 : 1 ≤ r := by linarith
  have hnear (c : A) : q ≤ (bundle g c).card := (hs c).1
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  rw [efx_iff_threshold M hr]
  intro v c hvc
  by_cases hvS : v ∈ S
  · by_cases hcS : c ∈ S
    · by_cases hvP : v = a ∨ v = b
      · by_cases hcP : c = a ∨ c = b
        · apply positive_comparison M hr1 (B.cheap v hvP)
          · have hl := (hs c).1
            have hu := (hs v).2
            omega
          · exact B.comparison_expensive v c hvP hcP hvc
        · have hcU : c ∈ S \ {a, b} := by
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            exact ⟨hcS, hcP⟩
          exact (B.threshold_bound hr hsf hL hvP).trans
            (near_whole_cost M hr (hnear c) ((hnear c).trans (hpairToU v c hvP hcU)))
      · have hvU : v ∈ S \ {a, b} := by
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨hvS, hvP⟩
        by_cases hcP : c = a ∨ c = b
        · have ht := one_expensive_threshold M hr (hU v hvU).2 (hs v).2 (hU v hvU).1
          have hcost := near_whole_cost M hr (hnear c) ((hnear c).trans (hUToPair v hvU c hcP))
          nlinarith only [ht, hcost, hqR, hr]
        · have hcU : c ∈ S \ {a, b} := by
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            exact ⟨hcS, hcP⟩
          exact hinternal v hvU c hcU hvc
    · have hcost := expensive_lower_cost M hr (hnear c)
          (by rw [htoH v hvS c hcS]; exact hnear c)
      by_cases hvP : v = a ∨ v = b
      · have ht := B.threshold_bound hr hsf hL hvP
        nlinarith only [ht, hcost, hr]
      · have hvU : v ∈ S \ {a, b} := by
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨hvS, hvP⟩
        have ht := one_expensive_threshold M hr (hU v hvU).2 (hs v).2 (hU v hvU).1
        nlinarith only [ht, hcost, hqR, hr]
  · have ht := all_cheap_threshold_bound M (hH v hvS) (hs v).2 r
    have hsz : (q : ℝ) ≤ (bundle g c).card := by exact_mod_cast (hs c).1
    exact ht.trans (hsz.trans (cost_ge_size M hr1 g v c))

end ResearchMain.Chores
