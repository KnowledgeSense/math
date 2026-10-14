import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset

namespace HilbertBipartite

def partialBinomial (M N : ℕ) (x : ℚ) : ℚ :=
  ∑ l ∈ range (M + 1), x ^ l * (N.choose l : ℚ)

def signedPartial (M N : ℕ) : ℚ :=
  (-1) ^ M * partialBinomial M N (-1 / 2)

@[simp] theorem partialBinomial_zero (N : ℕ) (x : ℚ) :
    partialBinomial 0 N x = 1 := by
  simp [partialBinomial]

theorem partialBinomial_full (N : ℕ) (x : ℚ) :
    partialBinomial N N x = (x + 1) ^ N := by
  simpa [partialBinomial] using (add_pow x 1 N).symm

theorem partialBinomial_recurrence (M N : ℕ) (x : ℚ) :
    partialBinomial (M + 1) (N + 1) x =
      partialBinomial (M + 1) N x + x * partialBinomial M N x := by
  unfold partialBinomial
  rw [sum_range_succ', sum_range_succ' (fun l => x ^ l * (N.choose l : ℚ))]
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  simp_rw [Nat.choose_succ_succ', Nat.cast_add, mul_add, pow_succ]
  rw [sum_add_distrib, mul_sum]
  have h : (∑ l ∈ range (M + 1), x ^ l * x * (N.choose l : ℚ)) =
      ∑ l ∈ range (M + 1), x * (x ^ l * (N.choose l : ℚ)) := by
    apply sum_congr rfl
    intro l _
    ring
  rw [h]
  ring

theorem partialBinomial_boundary (M : ℕ) (x : ℚ) :
    partialBinomial M (M + 1) x = (x + 1) ^ (M + 1) - x ^ (M + 1) := by
  have h := partialBinomial_full (M + 1) x
  unfold partialBinomial at h ⊢
  rw [sum_range_succ] at h
  simp only [Nat.choose_self, Nat.cast_one, mul_one] at h
  linarith

@[simp] theorem signedPartial_zero (N : ℕ) : signedPartial 0 N = 1 := by
  simp [signedPartial]

theorem signedPartial_recurrence (M N : ℕ) :
    signedPartial (M + 1) (N + 1) =
      signedPartial (M + 1) N + (1 / 2) * signedPartial M N := by
  unfold signedPartial
  rw [partialBinomial_recurrence, pow_succ]
  ring

theorem signedPartial_boundary_nonneg (M : ℕ) : 0 ≤ signedPartial M (M + 1) := by
  unfold signedPartial
  rw [partialBinomial_boundary]
  norm_num
  have h : (-1 : ℚ) ^ M = 1 ∨ (-1 : ℚ) ^ M = -1 := neg_one_pow_eq_or ℚ M
  have hp : (0 : ℚ) ≤ (1 / 2) ^ (M + 1) := by positivity
  rw [neg_pow (1 / 2 : ℚ), pow_succ (-1 : ℚ)]
  rcases h with h | h <;> rw [h] <;> nlinarith

theorem signedPartial_nonneg (M N : ℕ) (h : M < N) : 0 ≤ signedPartial M N := by
  induction N generalizing M with
  | zero => omega
  | succ N ih =>
    by_cases he : M = N
    · subst M
      exact signedPartial_boundary_nonneg N
    cases M with
    | zero => simp
    | succ M =>
      rw [signedPartial_recurrence]
      have h1 := ih M (by omega)
      have h2 := ih (M + 1) (by omega)
      linarith


def signedBinomialCoefficient (m i c : ℕ) : ℚ :=
  (1 / 2) ^ c * ((i - 1).choose c : ℚ) * signedPartial (m - 1 - c) (i - 1 - c)

theorem signedBinomialCoefficient_nonneg (m i c : ℕ) (hm : 1 ≤ m) (hi : m < i) :
    0 ≤ signedBinomialCoefficient m i c := by
  unfold signedBinomialCoefficient
  by_cases hc : c ≤ m - 1
  · exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (signedPartial_nonneg _ _ (by omega))
  · have hz : m - 1 - c = 0 := by omega
    rw [hz, signedPartial_zero, mul_one]
    positivity

theorem signedBinomialCoefficient_top_pos (m i : ℕ) (hm : 1 ≤ m) (hi : m < i) :
    0 < signedBinomialCoefficient m i (m - 1) := by
  unfold signedBinomialCoefficient
  rw [Nat.sub_self, signedPartial_zero, mul_one]
  apply mul_pos (by positivity)
  exact_mod_cast Nat.choose_pos (by omega : m - 1 ≤ i - 1)

end HilbertBipartite
