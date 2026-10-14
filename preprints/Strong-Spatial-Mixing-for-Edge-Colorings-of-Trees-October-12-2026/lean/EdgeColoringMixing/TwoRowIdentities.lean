import EdgeColoringMixing.ConditionalInjections
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace EdgeColoringMixing.WeightedInjection
open Finset

variable {d q : ℕ}

/-- Partition by the first-row color without dropping its exact forbidden-color normalizer. -/
theorem partition_by_head_color (W : Fin (d + 1) → Fin q → ℝ) :
    partition W = ∑ c, W 0 c * partition (withoutColor (fun i : Fin d => W i.succ) c) := by
  have hsum (σ : Injection (d + 1) q) : weight W σ = ∑ c, weight W σ * cell 0 c σ := by
    rw [← Finset.mul_sum, row_sum, mul_one]
  change (∑ σ : Injection (d + 1) q, weight W σ) = _
  calc
    _ = ∑ σ : Injection (d + 1) q, ∑ c, weight W σ * cell 0 c σ :=
      Finset.sum_congr rfl (fun σ _ => hsum σ)
    _ = ∑ c, ∑ σ : Injection (d + 1) q, weight W σ * cell 0 c σ := Finset.sum_comm
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro c _
  exact head_numerator_eq W c

@[simp] theorem partition_one (W : Fin 1 → Fin q → ℝ) :
    partition W = ∑ c, W 0 c := by
  rw [partition_by_head_color]
  simp [partition, weight]

@[simp] theorem numerator_one_cell (W : Fin 1 → Fin q → ℝ) (c : Fin q) :
    numerator W (cell 0 c) = W 0 c := by
  change (∑ σ : Injection 1 q, weight W σ * cell 0 c σ) = _
  rw [head_numerator_eq]
  simp [partition, weight]

/-- The exact two-row partition function. -/
theorem partition_two (W : Fin 2 → Fin q → ℝ) :
    partition W = (∑ c, W 0 c) * (∑ c, W 1 c) - ∑ c, W 0 c * W 1 c := by
  rw [partition_by_head_color]
  simp_rw [partition_one]
  change (∑ c, W 0 c * (∑ b, if b = c then 0 else W 1 b)) = _
  simp_rw [sum_withoutColor, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]

theorem mean_two_zero (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (c : Fin q) :
    mean (law W hW.nonneg (partition_pos W hW)) 0 c =
      W 0 c * ((∑ b, W 1 b) - W 1 c) / partition W := by
  rw [head_marginal_eq, partition_one]
  change W 0 c * (∑ b, if b = c then 0 else W 1 b) / partition W = _
  rw [sum_withoutColor]

theorem mean_two_one (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (c : Fin q) :
    mean (law W hW.nonneg (partition_pos W hW)) 1 c =
      W 1 c * ((∑ b, W 0 b) - W 0 c) / partition W := by
  let e := Equiv.swap (0 : Fin 2) 1
  have hW' : RowSurplus (fun j => W (e j)) s :=
    ⟨hW.positive, fun j b => hW.nonneg (e j) b, fun j b => hW.le_one (e j) b,
      fun j => hW.row_mass (e j)⟩
  have h := mean_two_zero (fun j => W (e j)) hW' c
  rw [marginal_reindex W hW e 0 c, partition_reindex] at h
  simpa [e] using h

/-- The exact cross-row mixed moment, including the same-color exclusion. -/
theorem mixed_moment_two (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (c b : Fin q) :
    (law W hW.nonneg (partition_pos W hW)).expectation
      (fun σ => cell 0 c σ * cell 1 b σ) =
      (if b = c then 0 else W 0 c * W 1 b) / partition W := by
  rw [← weightedExpectation_eq]
  unfold weightedExpectation
  congr 1
  change numerator W (fun σ => cell 0 c σ * cell 0 b (tailInjection σ)) = _
  rw [head_observable_numerator, numerator_one_cell]
  unfold withoutColor
  split_ifs <;> simp

end EdgeColoringMixing.WeightedInjection
