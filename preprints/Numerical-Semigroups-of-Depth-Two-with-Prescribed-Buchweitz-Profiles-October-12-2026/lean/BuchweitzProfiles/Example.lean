import BuchweitzProfiles.Reflection
import BuchweitzProfiles.Data.Example
import Mathlib.Tactic.NormNum

open scoped Pointwise

namespace BuchweitzProfiles

def exampleG : Finset Nat := gapset 169 exampleC

lemma exampleC_bound : ∀ c ∈ exampleC, c ≤ 169 - 2 := by
  intro c hc
  simp only [exampleC, Finset.mem_insert, Finset.mem_singleton] at hc
  omega

lemma exampleC_zero : 0 ∈ exampleC := by decide
lemma exampleC_positive : ∃ c ∈ exampleC, 0 < c := ⟨26, by decide, by decide⟩

/-- The actual numerical semigroup underlying the example. -/
def exampleSemigroup : NumericalSemigroup :=
  depthTwoSemigroup (by decide : 3 ≤ 169) exampleC_bound

theorem example_multiplicity : IsMultiplicity exampleSemigroup 169 :=
  depthTwo_multiplicity (by decide) exampleC_bound

theorem example_conductor : IsConductor exampleSemigroup 338 :=
  depthTwo_conductor (by decide) exampleC_bound exampleC_zero

theorem example_gapset (n : Nat) : n ∈ exampleG ↔ ¬ n ∈ exampleSemigroup := by
  change n ∈ gapset 169 exampleC ↔ ¬ ¬ ReflectedGap 169 (· ∈ exampleC) n
  rw [not_not]
  exact mem_gapset_iff (by decide) exampleC_bound n

theorem example_genus : exampleG.card = 172 := by
  rw [exampleG, gapset_card (by decide) exampleC_bound]
  decide

lemma filter_sumset_succ (C : Finset Nat) (m n : Nat) :
    (sumset C (n + 1)).filter (· < m) =
      (((sumset C n).filter (· < m)) + C).filter (· < m) := by
  ext x
  simp only [Finset.mem_filter, mem_sumset_succ, Finset.mem_add]
  constructor
  · rintro ⟨⟨a, ha, b, hb, he⟩, hx⟩
    exact ⟨⟨a, ⟨ha, by omega⟩, b, hb, he⟩, hx⟩
  · rintro ⟨⟨a, ⟨ha, _⟩, b, hb, he⟩, hx⟩
    exact ⟨⟨a, ha, b, hb, he⟩, hx⟩


lemma example_tail_set (n : Nat) (hn : 6 ≤ n) :
    (sumset exampleC n).filter (· < 169) = (sumset exampleC 6).filter (· < 169) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [filter_sumset_succ, ih, ← filter_sumset_succ]
    exact example_stable


lemma example_tail_count (n : Nat) (hn : 6 ≤ n) :
    truncatedCount exampleC 169 n = 34 := by
  unfold truncatedCount
  rw [example_tail_set n hn]
  exact example_six_count

theorem example_beta_tail (n : Nat) (hn : 6 ≤ n) :
    beta exampleG n = 37 - 6 * (n : Int) := by
  rw [exampleG, beta_gapset exampleC 169 (by decide) exampleC_bound exampleC_zero
    exampleC_positive n (by omega), example_tail_count n hn]
  have : exampleC.card = 4 := by decide
  rw [this]
  ring

lemma example_beta_reduction (n : Nat) (hn : 1 ≤ n) :
    beta exampleG n = (truncatedCount exampleC 169 n : Int) - 3 * (2 * (n : Int) - 1) := by
  rw [exampleG, beta_gapset exampleC 169 (by decide) exampleC_bound exampleC_zero
    exampleC_positive n hn]
  have : exampleC.card = 4 := by decide
  rw [this]
  ring


/-- The complete Buchweitz set, including exclusion of every later order. -/
theorem example_buchweitz_set (n : Nat) :
    (2 ≤ n ∧ 0 < beta exampleG n) ↔ n = 3 ∨ n = 6 := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ := example_small_counts
  by_cases ht : 6 ≤ n
  · rw [example_beta_tail n ht]
    omega
  by_cases h2 : 2 ≤ n
  · have hcases : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;>
      rw [example_beta_reduction _ (by omega)] <;>
      simp_all
  · constructor
    · exact fun h => False.elim (h2 h.1)
    · intro h; omega

end BuchweitzProfiles
