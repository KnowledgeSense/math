import MainTheorems.Chores.IsolatedRepair
import MainTheorems.Chores.NoDonors
import MainTheorems.Chores.BoundaryDonor

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

theorem unique_ordinary_reduction (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} (hf : Optimal M S f₀ f)
    (hs : ∀ v, Fintype.card E / Fintype.card A ≤ (bundle f v).card ∧
      (bundle f v).card ≤ Fintype.card E / Fintype.card A + 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hunique : UniqueBad M S f a b)
    (hL : expensiveCount M f b b + 2 ≤ Fintype.card E / Fintype.card A)
    {μ : ℝ} (hmax : MaxDeficient M μ S)
    (hμ : μ * Fintype.card A = Fintype.card E) (hH : 2 ≤ Sᶜ.card) :
    (∃ g : E → A, EFX M r g) ∨ ∃ k ∈ S, k ≠ a ∧ k ≠ b ∧
      0 < expensiveCount M f k k ∧ expensiveCount M f b b + 3 ≤ Fintype.card E / Fintype.card A := by
  classical
  by_cases hS : S = {a, b}
  · subst S
    left
    apply isolated_optimal_pair M hf hs hunique.1 (by omega) hmax hμ hH hr
  · have hU : (S \ {a, b}).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro ht
      have hsub : S ⊆ ({a, b} : Finset A) := Finset.sdiff_eq_empty_iff_subset.mp ht
      have hpair : ({a, b} : Finset A) ⊆ S := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with hv | hv <;> subst v
        · exact ha
        · exact hb
      exact hS (Finset.Subset.antisymm hsub hpair)
    by_cases hd : ∃ k ∈ S, k ≠ a ∧ k ≠ b ∧ 0 < expensiveCount M f k k
    · obtain ⟨k, hkS, hka, hkb, hkpos⟩ := hd
      by_cases hboundary : expensiveCount M f b b + 2 = Fintype.card E / Fintype.card A
      · exact Or.inl (boundary_donor M hr hf hs ha hb hkS hunique hka hkb hboundary hkpos)
      · exact Or.inr ⟨k, hkS, hka, hkb, hkpos, by omega⟩
    · left
      apply no_outside_donors M hr hf hs ha hb hunique hL hU
      intro k hkS hka hkb
      by_contra hk
      exact hd ⟨k, hkS, hka, hkb, by omega⟩

end ResearchMain.Chores
