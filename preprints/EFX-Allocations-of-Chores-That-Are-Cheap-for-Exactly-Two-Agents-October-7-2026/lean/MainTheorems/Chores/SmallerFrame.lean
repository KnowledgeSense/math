import MainTheorems.Chores.IsolatedSwapCounts
import MainTheorems.Chores.OneFiller
import MainTheorems.Chores.FrameEFX

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

structure SmallerFrame (M : TwoCheapModel A E) (S : Finset A) (f g : E → A) (a b : A) (q : ℕ) : Prop where
  size : ∀ c, q ≤ (bundle g c).card ∧ (bundle g c).card ≤ q + 1
  pair : OrdinaryStats M f g a b
  own : ∀ v ∈ S \ {a, b}, expensiveCount M g v v ≤ 1 ∧ OwnCheap M g v
  high_whole : ∀ v ∈ S \ {a, b}, expensiveCount M g v a = (bundle g a).card
  low_bound : ∀ v ∈ S \ {a, b}, (bundle g b).card ≤ expensiveCount M g v b + 1
  pair_bound : ∀ v c, (v = a ∨ v = b) → c ∈ S \ {a, b} →
    (bundle g c).card ≤ expensiveCount M g v c + 1
  outside_cheap : ∀ v, v ∉ S → ∀ e ∈ bundle g v, M.Cheap v e
  to_outside : ∀ v ∈ S, ∀ c, c ∉ S → expensiveCount M g v c = (bundle g c).card

namespace IsolatedSwap

variable {M : TwoCheapModel A E} {S : Finset A} {f : E → A} {a b k : A}

theorem smaller_frame (B : IsolatedSwap M S f a b k) {f₀ g : E → A} {q : ℕ}
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b) (hq : 2 ≤ q)
    (hz : ∀ v ∈ B.outside, expensiveCount M f v v = 0)
    (hg : Feasible B.frozenModel B.outside B.allocation g) : SmallerFrame M S f g a b q := by
  have hs' (c : A) : q ≤ (bundle g c).card ∧ (bundle g c).card ≤ q + 1 := by
    rw [hg.2.1 c, B.card]
    exact hs c
  have houtside {v : A} (hv : v ∉ S) : bundle g v = bundle f v := by
    rw [feasible_outside_bundle B.frozenModel hg (fun ht => hv (Finset.mem_sdiff.mp ht).1)]
    exact B.other_bundle (by intro ht; subst v; exact hv B.donor_mem)
      (by intro ht; subst v; exact hv hb)
  have hown {v : A} (hv : v ∈ B.outside) : expensiveCount M g v v ≤ 1 ∧ OwnCheap M g v := by
    have ht := one_filler_expensive B.frozenModel hg B.token_inside
      (fun e he => B.frozen_filler_iff hz he) hv
    have heq := frozen_expensive_eq M B.outside B.allocation a b B.pair_distinct hg hv v
    have he : expensiveCount M g v v ≤ 1 := by
      change expensiveCount B.frozenModel g v v = expensiveCount M g v v at heq
      rw [heq] at ht
      split_ifs at ht <;> omega
    refine ⟨he, ?_⟩
    rw [ownCheap_iff_count]
    have hsum := cheap_add_expensive M g v v
    have hsz := (hs' v).1
    omega
  refine ⟨hs', (B.pair_stats hf hs ha hb hbad).of_pair_bundles
    (fun v hv => B.feasible_pair_bundle hg hv), fun v hv => hown hv, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hvs := Finset.mem_sdiff.mp hv
    have hva : v ≠ a := by intro ht; exact hvs.2 (by simp [ht])
    have hvb : v ≠ b := by intro ht; exact hvs.2 (by simp [ht])
    unfold expensiveCount
    rw [B.feasible_pair_bundle hg (Or.inl rfl), B.other_bundle B.donor_high.symm B.pair_distinct]
    change expensiveCount M f v a = (bundle f a).card
    exact pure_outside_expensive M hf.1.1 B.pair_distinct
      (optimal_bad_source_pure M hf hs ha hb hbad) hvs.1 hva hvb
  · intro v hv
    unfold expensiveCount
    rw [B.feasible_pair_bundle hg (Or.inr rfl)]
    exact B.outside_to_pair_bound hf hs ha hb hbad hv (Or.inr rfl)
  · intro v c hv hc
    exact B.feasible_pair_to_outside hz hg hv hc
  · intro v hv e he
    rw [houtside hv] at he
    have ho := (mem_bundle f v e).mp he
    have hcheap := separated_outside_cheap M hf.1.1 (e := e) (by rwa [ho])
    rwa [ho] at hcheap
  · intro v hv c hc
    unfold expensiveCount
    rw [houtside hc]
    change expensiveCount M f v c = (bundle f c).card
    exact separated_outside_target_expensive M hf.1.1 hv hc

theorem no_bad_efx (B : IsolatedSwap M S f a b k) {f₀ g : E → A} {q : ℕ}
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b)
    (hL : expensiveCount M f b b + 2 ≤ q)
    (hz : ∀ v ∈ B.outside, expensiveCount M f v v = 0)
    (hg : Optimal B.frozenModel B.outside B.allocation g)
    (hnone : ∀ v ∈ B.outside, ∀ c ∈ B.outside, ¬Bad B.frozenModel g v c)
    {r : ℝ} (hr : 2 < r) : EFX M r g := by
  have hq : 2 ≤ q := by omega
  have C := B.smaller_frame hf hs ha hb hbad hq hz hg.1
  apply isolated_frame_efx M hr hq C.size (fun c => (hs c).2) C.pair hL C.own
    ?_ C.pair_bound ?_ C.outside_cheap C.to_outside
  · intro v hv c hc hvc
    have hθ := frozen_threshold_eq M B.outside B.allocation a b B.pair_distinct hg.1 hv r
    have hcost := frozen_cost_eq M B.outside B.allocation a b B.pair_distinct hg.1 hc r v
    change threshold B.frozenModel r g v = threshold M r g v at hθ
    change bundleCost B.frozenModel r v (bundle g c) = bundleCost M r v (bundle g c) at hcost
    rw [← hθ, ← hcost]
    apply separated_comparison B.frozenModel hr (hg.energyMinimum B.frozenModel) C.size hvc
    exact fun hv' hc' hbad' => hnone v hv' c hc' hbad'
  · intro v hv c hc
    rcases hc with hc | hc <;> subst c
    · rw [C.high_whole v hv]
      omega
    · exact C.low_bound v hv

end IsolatedSwap

end ResearchMain.Chores
