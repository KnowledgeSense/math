import MainTheorems.Chores.PairReversal

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

theorem zero_donor_high (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b k : A} (ha : a ∈ S) (hb : b ∈ S) (hkS : k ∈ S)
    (hunique : UniqueBad M S f a b) (hka : k ≠ a) (hkb : k ≠ b)
    (hk : expensiveCount M f k k = 0) (hL : expensiveCount M f b b + 2 ≤ q)
    {d : E} (hd : d ∈ bundle f k) (hcheap : M.Cheap a d) :
    ∃ g : E → A, EFX M r g := by
  have hbound := minimum_exchange_bound M (hf.energyMinimum M) ha hkS hka.symm hd hcheap
  have hcounts := (minimum_bad_counts M (hf.energyMinimum M) hs ha hb hunique.1).1
  have he : expensiveCount M f k k = expensiveCount M f b b := by omega
  exact neutral_handoff M hr hf hs ha hb hkS hunique hka hkb he hL hd hcheap

theorem zero_donor_either_endpoint (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b k : A} (ha : a ∈ S) (hb : b ∈ S) (hkS : k ∈ S)
    (hunique : UniqueBad M S f a b) (hka : k ≠ a) (hkb : k ≠ b)
    (hk : expensiveCount M f k k = 0) (hL : expensiveCount M f b b + 2 ≤ q)
    {d : E} (hd : d ∈ bundle f k) (hcheap : M.Cheap a d ∨ M.Cheap b d) :
    ∃ g : E → A, EFX M r g := by
  rcases hcheap with hcheap | hcheap
  · exact zero_donor_high M hr hf hs ha hb hkS hunique hka hkb hk hL hd hcheap
  · obtain ⟨B⟩ := exists_basic_exchange M hf.1.1 hs ha hb hunique.1
    obtain ⟨hunique', hf', hEa⟩ := B.reverse_unique_pair hf hs hunique
    have hk' : expensiveCount M B.allocation k k = 0 := by rw [B.other_expensive k hka hkb, hk]
    have hL' : expensiveCount M B.allocation a a + 2 ≤ q := by rwa [hEa]
    have hd' : d ∈ bundle B.allocation k := by rw [B.other_bundle hka hkb]; exact hd
    exact zero_donor_high M hr hf' (B.balanced hs) hb ha hkS hunique' hkb hka hk' hL' hd' hcheap

end ResearchMain.Chores
