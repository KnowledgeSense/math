import MainTheorems.Chores.SmallerRepair
import MainTheorems.Chores.PairIsolation

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

theorem no_outside_donors (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ v, q ≤ (bundle f v).card ∧ (bundle f v).card ≤ q + 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hunique : UniqueBad M S f a b)
    (hL : expensiveCount M f b b + 2 ≤ q) (hU : (S \ {a, b}).Nonempty)
    (hz : ∀ v ∈ S, v ≠ a → v ≠ b → expensiveCount M f v v = 0) :
    ∃ g : E → A, EFX M r g := by
  rcases zero_donors_or_isolated M hr hf hs ha hb hunique hL hz with hefx | hiso
  · exact hefx
  · have hq : 2 ≤ q := by omega
    obtain ⟨k, hkU⟩ := hU
    have hkS := (Finset.mem_sdiff.mp hkU).1
    have hka : k ≠ a := by intro ht; exact (Finset.mem_sdiff.mp hkU).2 (by simp [ht])
    have hkb : k ≠ b := by intro ht; exact (Finset.mem_sdiff.mp hkU).2 (by simp [ht])
    have hOwnK : OwnCheap M f k := by
      rw [ownCheap_iff_count]
      have hsum := cheap_add_expensive M f k k
      have he := hz k hkS hka hkb
      have hsize := (hs k).1
      omega
    obtain ⟨e, he, heCheap⟩ := hOwnK
    obtain ⟨d, hd, hdCheap⟩ := bad_target_ownCheap M hf.1.1 hs ha hunique.1
    have hdHigh := minimum_bad_target_pure M (hf.energyMinimum M) hs ha hb hunique.1 d hd hdCheap
    let B : IsolatedSwap M S f a b k :=
      { firstChore := e
        secondChore := d
        firstOwner := (mem_bundle f k e).mp he
        secondOwner := (mem_bundle f b d).mp hd
        donor_mem := hkS
        pair_distinct := hunique.1.1
        donor_high := hka
        donor_low := hkb
        donorCheap := heCheap
        highCheap := hdHigh
        lowCheap := hdCheap
        isolated := hiso }
    have hzB (v : A) (hv : v ∈ B.outside) : expensiveCount M f v v = 0 := by
      have ht := Finset.mem_sdiff.mp hv
      apply hz v ht.1
      · intro heq
        exact ht.2 (by simp [heq])
      · intro heq
        exact ht.2 (by simp [heq])
    have hsB (v : A) : q ≤ (bundle B.allocation v).card ∧ (bundle B.allocation v).card ≤ q + 1 := by
      rw [B.card]
      exact hs v
    obtain ⟨g, hg, _, hcases⟩ := one_filler_optimal B.frozenModel B.outside B.allocation
      (B.frozen_separated hzB) hsB B.token_inside (fun x hx => B.frozen_filler_iff hzB hx)
    rcases hcases with hnone | hpair
    · exact ⟨g, B.no_bad_efx hf hs ha hb hunique.1 hL hzB hg hnone hr⟩
    · obtain ⟨c, w, hc, hw, hsmall, _, hzero⟩ := hpair
      exact B.repair_small_pair hf hs ha hb hunique.1 hL hzB hg hc hw hsmall hzero hr

end ResearchMain.Chores
