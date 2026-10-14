import SphericalTreeFailures.PartitionRecursion
import Mathlib.Tactic.FieldSimp

namespace SphericalTreeFailures
open Polynomial Finset

/-- Unnormalized activity weight, indexed by actual independent-set size. -/
noncomputable def sizeWeight (m n j : ℕ) (activity : ℝ) : ℝ :=
  coefficient m n j * activity ^ j

noncomputable def sizeProbability (m n j : ℕ) (activity : ℝ) : ℝ :=
  sizeWeight m n j activity / totalPartition m n activity

theorem totalPartition_sum (m n : ℕ) (activity : ℝ) :
    totalPartition m n activity =
      ∑ s ∈ independentSetsWithin (sphericalTree m n).graph univ, activity ^ s.card := by
  simp [totalPartition, independencePolynomial, eval₂_finsetSum]

theorem totalPartition_pos (m n : ℕ) {activity : ℝ} (ha : 0 < activity) :
    0 < totalPartition m n activity := by
  rw [totalPartition_sum]
  apply sum_pos'
  · intro s hs
    exact le_of_lt (pow_pos ha _)
  · refine ⟨∅, ?_, by simp⟩
    exact (mem_independentSetsWithin _).mpr ⟨empty_subset _, independent_empty _⟩

theorem sizeProbability_nonneg (m n j : ℕ) {activity : ℝ} (ha : 0 < activity) :
    0 ≤ sizeProbability m n j activity := by
  unfold sizeProbability sizeWeight
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_of_lt (pow_pos ha _)))
    (le_of_lt (totalPartition_pos m n ha))

/-- Activity tilting preserves the sign of every interior log-concavity defect. -/
theorem tilting_preserves_failure (m n j : ℕ) {activity : ℝ} (ha : 0 < activity) :
    sizeProbability m n j activity * sizeProbability m n (j + 2) activity >
      sizeProbability m n (j + 1) activity ^ 2 ↔
    coefficient m n j * coefficient m n (j + 2) > coefficient m n (j + 1) ^ 2 := by
  have hz := totalPartition_pos m n ha
  have hfactor : 0 < activity ^ (2 * j + 2) / totalPartition m n activity ^ 2 :=
    div_pos (pow_pos ha _) (pow_pos hz _)
  have he :
      sizeProbability m n j activity * sizeProbability m n (j + 2) activity -
        sizeProbability m n (j + 1) activity ^ 2 =
      (activity ^ (2 * j + 2) / totalPartition m n activity ^ 2) *
        ((coefficient m n j : ℝ) * coefficient m n (j + 2) -
          coefficient m n (j + 1) ^ 2) := by
    unfold sizeProbability sizeWeight
    simp only [pow_add, pow_mul]
    ring
  constructor
  · intro h
    have hp : 0 < sizeProbability m n j activity * sizeProbability m n (j + 2) activity -
        sizeProbability m n (j + 1) activity ^ 2 := sub_pos.mpr h
    rw [he] at hp
    have hc := sub_pos.mp ((mul_pos_iff_of_pos_left hfactor).mp hp)
    exact_mod_cast hc
  · intro h
    have hc : (coefficient m n (j + 1) : ℝ) ^ 2 <
        coefficient m n j * coefficient m n (j + 2) := by exact_mod_cast h
    apply sub_pos.mp
    rw [he]
    exact mul_pos hfactor (sub_pos.mpr hc)

end SphericalTreeFailures
