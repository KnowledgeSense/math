import MainTheorems.AHOConstants.ArcCapacities
import MainTheorems.AHOConstants.IntervalCriterion
import MainTheorems.AHOConstants.CounterexampleExponents

namespace ResearchMain.AHOConstants

open scoped BigOperators

variable {m : ℕ}

theorem feasible_iff_cuts (p q : Fin (m + 1) → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hp₁ : (∑ i, p i) = 1) (hq₁ : (∑ i, q i) = 1) :
    Feasible p q ↔ ∀ S T, 1 ≤ cutCapacity p q S T := by
  have ht : (∑ i, p i) = ∑ i, q i := hp₁.trans hq₁.symm
  constructor
  · rintro ⟨a, b, h⟩ S T
    exact h.cut_lower_bound hq₁ S T
  · intro hc
    rw [feasible_iff_scalar_bounds p q ht]
    intro i j
    by_cases hij : i = j
    · subst j
      have hqi : q i ≤ 1 := by
        calc
          q i ≤ ∑ t, q t := Finset.single_le_sum (fun t _ => hq t) (Finset.mem_univ i)
          _ = 1 := hq₁
      exact ⟨by linarith, by linarith [hq i], by linarith, by linarith⟩
    · have h₁ := hc ((cyclicArc i j).image (finRotate (m + 1))) (cyclicArc i j)ᶜ
      have h₂ := hc ((cyclicArc i j).image (finRotate (m + 1))) (insert j (cyclicArc i j))ᶜ
      have h₃ := hc ((cyclicArc i j).image (finRotate (m + 1))) ((cyclicArc i j).erase i)ᶜ
      have h₄ := hc ((cyclicArc i j).image (finRotate (m + 1)))
        (insert j ((cyclicArc i j).erase i))ᶜ
      rw [arc_capacity_first p q ht hq₁ hij] at h₁
      rw [arc_capacity_zero p q ht hq₁ hij] at h₂
      rw [arc_capacity_two p q ht hq₁ hij] at h₃
      rw [arc_capacity_second p q ht hq₁ hij] at h₄
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem infeasible_strict_cut (p q : Fin (m + 1) → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hp₁ : (∑ i, p i) = 1) (hq₁ : (∑ i, q i) = 1)
    (h : ¬Feasible p q) : ∃ S T, cutCapacity p q S T < 1 := by
  rw [feasible_iff_cuts p q hq hp₁ hq₁] at h
  push Not at h
  exact h

noncomputable def strictCutExponents (p q : Fin (m + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp₁ : (∑ i, p i) = 1) (hq₁ : (∑ i, q i) = 1)
    (S T : Finset (Fin (m + 1))) (hcut : cutCapacity p q S T < 1) : CutExponents where
  theta := 2 - cutMass p S - cutMass q T
  edges := (cutEdges S T).card
  theta_nonnegative := by
    have hS := cutMass_le_total hp S
    have hT := cutMass_le_total hq T
    rw [hp₁] at hS
    rw [hq₁] at hT
    linarith
  edges_le_one := strict_cut_has_at_most_one_edge hp hq hp₁ hq₁ hcut
  capacity_gap := hcut

end ResearchMain.AHOConstants
