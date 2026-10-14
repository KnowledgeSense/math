import MainTheorems.Chores.IsolatedPair
import MainTheorems.Chores.ZeroDonor

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

theorem pair_isolated_or_external_chore (M : TwoCheapModel A E)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b) :
    IsolatedPair M a b ∨ ∃ k ∈ S, k ≠ a ∧ k ≠ b ∧
      ∃ d ∈ bundle f k, M.Cheap a d ∨ M.Cheap b d := by
  classical
  by_cases hex : ∃ k ∈ S, k ≠ a ∧ k ≠ b ∧ ∃ d ∈ bundle f k, M.Cheap a d ∨ M.Cheap b d
  · exact Or.inr hex
  · left
    have hp := optimal_bad_source_pure M hf hs ha hb hbad
    have hq := minimum_bad_target_pure M (hf.energyMinimum M) hs ha hb hbad
    intro e he
    have ht : M.first e ∈ S ∨ M.second e ∈ S := by
      rcases he with hc | hc
      · rcases hc with hc | hc
        · exact Or.inl (hc ▸ ha)
        · exact Or.inr (hc ▸ ha)
      · rcases hc with hc | hc
        · exact Or.inl (hc ▸ hb)
        · exact Or.inr (hc ▸ hb)
    have howner := hf.1.1 e
    rw [separatedAllowed, ite_eq_left ht, Finset.mem_inter, mem_endpointAllowed] at howner
    have heb : e ∈ bundle f (f e) := (mem_bundle f (f e) e).mpr rfl
    by_cases hea : f e = a
    · have hc : M.Cheap a e := by simpa only [hea] using howner.1
      have hb' := hp e (by rwa [hea] at heb) hc
      exact ⟨hc, hb'⟩
    · by_cases heb' : f e = b
      · have hc : M.Cheap b e := by simpa only [heb'] using howner.1
        have ha' := hq e (by rwa [heb'] at heb) hc
        exact ⟨ha', hc⟩
      · exact False.elim (hex ⟨f e, howner.2, hea, heb', e, heb, he⟩)

theorem zero_donors_or_isolated (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hunique : UniqueBad M S f a b)
    (hL : expensiveCount M f b b + 2 ≤ q)
    (hz : ∀ k ∈ S, k ≠ a → k ≠ b → expensiveCount M f k k = 0) :
    (∃ g : E → A, EFX M r g) ∨ IsolatedPair M a b := by
  rcases pair_isolated_or_external_chore M hf hs ha hb hunique.1 with hiso | hex
  · exact Or.inr hiso
  · obtain ⟨k, hkS, hka, hkb, d, hd, hcheap⟩ := hex
    exact Or.inl (zero_donor_either_endpoint M hr hf hs ha hb hkS hunique hka hkb
      (hz k hkS hka hkb) hL hd hcheap)

end ResearchMain.Chores
