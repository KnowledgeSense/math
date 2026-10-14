import MainTheorems.Chores.ForeignExchange

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

def UniqueBad (M : TwoCheapModel A E) (S : Finset A) (f : E → A) (a b : A) : Prop :=
  Bad M f a b ∧ ∀ c ∈ S, ∀ d ∈ S, Bad M f c d → c = a ∧ d = b

omit [DecidableEq E] in
theorem UniqueBad.count (M : TwoCheapModel A E) {S : Finset A} {f : E → A} {a b : A}
    (h : UniqueBad M S f a b) (ha : a ∈ S) (hb : b ∈ S) : badCount M S f = 1 := by
  have heq : ((S ×ˢ S).filter (fun p => Bad M f p.1 p.2)) = {(a, b)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
    constructor
    · intro hp
      have h' := h.2 p.1 hp.1.1 p.2 hp.1.2 hp.2
      exact Prod.ext h'.1 h'.2
    · intro hp
      subst p
      exact ⟨⟨ha, hb⟩, h.1⟩
  simp [badCount, heq]

namespace ForeignExchange

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ f : E → A} {a b k : A} {q : ℕ}

theorem pair_expensive_bound (B : ForeignExchange M S f a b k)
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hbad : Bad M f a b) (hL : expensiveCount M f b b + 2 ≤ q)
    (hka : expensiveCount M f b b + 2 ≤ expensiveCount M f a k)
    (hkb : expensiveCount M f b b + 2 ≤ expensiveCount M f b k)
    {v d : A} (hv : v = a ∨ v = b) (hvd : v ≠ d) :
    expensiveCount M B.allocation v v ≤ expensiveCount M B.allocation v d := by
  have hcounts := (minimum_bad_counts M (hf.energyMinimum M) hs B.high_mem B.low_mem hbad).1
  have hhighPure := optimal_bad_source_pure M hf hs B.high_mem B.low_mem hbad
  have hlowPure := minimum_bad_target_pure M (hf.energyMinimum M) hs B.high_mem B.low_mem hbad
  have hhighObs := pure_observer_expensive M hf.1.1 B.low_mem hhighPure
  have hlowObs := pure_observer_expensive M hf.1.1 B.high_mem hlowPure
  have hvS : v ∈ S := hv.elim (fun h => h ▸ B.high_mem) (fun h => h ▸ B.low_mem)
  have hown : expensiveCount M B.allocation v v = expensiveCount M f b b + 1 := by
    rcases hv with rfl | rfl
    · rw [B.high_expensive, hcounts]
    · exact B.low_expensive
  rw [hown]
  by_cases hda : d = a
  · subst d
    have hvb : v = b := hv.resolve_left hvd
    subst v
    rw [B.other_expensive b B.donor_high.symm B.pair_distinct, hhighObs, hcounts]
  · by_cases hdb : d = b
    · subst d
      have hva : v = a := hv.resolve_right hvd
      subst v
      have h := B.target_count B.high_mem
      rw [ite_eq_left B.highCheap, hlowObs] at h
      omega
    · by_cases hdk : d = k
      · subst d
        have h := B.source_count hvS
        rcases hv with rfl | rfl
        · rw [ite_eq_left B.highCheap] at h
          omega
        · rw [ite_eq_left B.lowCheap] at h
          omega
      · rw [B.other_expensive v hdk hdb]
        by_cases hdS : d ∈ S
        · rcases hv with rfl | rfl
          · exact optimal_pair_high_margin M hf hs B.high_mem B.low_mem hdS hbad hda hdb
          · exact optimal_pair_low_margin M hf hs B.high_mem B.low_mem hdS hbad hda hdb
        · rw [separated_outside_target_expensive M hf.1.1 hvS hdS]
          have hsize := (hs d).1
          omega

theorem direct_efx (B : ForeignExchange M S f a b k) {r : ℝ} (hr : 2 < r)
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hunique : UniqueBad M S f a b) (hL : expensiveCount M f b b + 2 ≤ q)
    (hka : expensiveCount M f b b + 2 ≤ expensiveCount M f a k)
    (hkb : expensiveCount M f b b + 2 ≤ expensiveCount M f b k) : EFX M r B.allocation := by
  have hr1 : 1 ≤ r := by linarith
  have hsnew : ∀ c, q ≤ (bundle B.allocation c).card ∧ (bundle B.allocation c).card ≤ q + 1 := by
    intro c
    simpa only [B.card] using hs c
  have hhighOwn := B.high_ownCheap hunique.1.2.1
  have hlowOwn := B.low_ownCheap (optimal_bad_target_two_cheap M hf hs B.high_mem B.low_mem hunique.1)
  rw [efx_iff_threshold M hr]
  intro v d hvd
  by_cases hv : v = a ∨ v = b
  · have hown : OwnCheap M B.allocation v := hv.elim (fun h => h ▸ hhighOwn) (fun h => h ▸ hlowOwn)
    have hsize : (bundle B.allocation v).card ≤ (bundle B.allocation d).card + 1 := by
      have hvsize := (hsnew v).2
      have hdsize := (hsnew d).1
      omega
    exact positive_comparison M hr1 hown hsize
      (B.pair_expensive_bound hf hs hunique.1 hL hka hkb hv hvd)
  · have hva : v ≠ a := fun h => hv (Or.inl h)
    have hvb : v ≠ b := fun h => hv (Or.inr h)
    rw [B.outsider_threshold r hvb]
    by_cases hvS : v ∈ S
    · rw [B.outsider_cost r hvS hva hvb d]
      apply separated_comparison M hr (hf.energyMinimum M) hs hvd
      intro hv' hd hbad
      exact hva (hunique.2 v hv' d hd hbad).1
    · have ht := separated_outside_threshold M hf.1.1 r hs hvS
      have hc := cost_ge_size M hr1 B.allocation v d
      have hsize : (q : ℝ) ≤ (bundle B.allocation d).card := by exact_mod_cast (hsnew d).1
      linarith

end ForeignExchange

theorem direct_buffer (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b k : A} (ha : a ∈ S) (hb : b ∈ S) (hk : k ∈ S)
    (hunique : UniqueBad M S f a b) (hka : k ≠ a) (hkb : k ≠ b)
    (hL : expensiveCount M f b b + 2 ≤ q) (hkpos : 0 < expensiveCount M f k k)
    (hmarginA : expensiveCount M f b b + 2 ≤ expensiveCount M f a k)
    (hmarginB : expensiveCount M f b b + 2 ≤ expensiveCount M f b k) :
    ∃ g : E → A, EFX M r g := by
  obtain ⟨e, he, hecheap⟩ := own_expensive_exists M hkpos
  have hlowOwn := bad_target_ownCheap M hf.1.1 hs ha hunique.1
  obtain ⟨d, hd, hdcheap⟩ := hlowOwn
  have hlowPure := minimum_bad_target_pure M (hf.energyMinimum M) hs ha hb hunique.1
  have heq := (mem_bundle f k e).mp he
  have hdq := (mem_bundle f b d).mp hd
  have hfill := separated_expensive_filler M hf.1.1 (e := e) (by rw [heq]; exact hecheap)
  let B : ForeignExchange M S f a b k :=
    ⟨e, d, heq, hdq, ha, hb, hk, hunique.1.1, hka, hkb, hfill, hlowPure d hd hdcheap, hdcheap⟩
  exact ⟨B.allocation, B.direct_efx hr hf hs hunique hL hmarginA hmarginB⟩

end ResearchMain.Chores
