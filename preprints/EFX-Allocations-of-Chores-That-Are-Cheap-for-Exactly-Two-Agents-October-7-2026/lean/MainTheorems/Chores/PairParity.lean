import MainTheorems.Chores.CollapsedHall
import Mathlib.Algebra.Group.Nat.Even

namespace ResearchMain.Chores

theorem pair_aggregate_choice {n m q s C : ℕ} {μ : ℝ}
    (hn : 4 ≤ n) (hq : 2 ≤ q) (hm : m = q * n + s)
    (hμ : μ * n = m) (hqu : μ < q + 1) (hC : (C : ℝ) ≤ 2 * μ) :
    ∃ T : ℕ, C ≤ T ∧ Even (T - C) ∧ T + q * (n - 2) ≤ m ∧
      (2 * μ < (T : ℝ) + 1 ∨ μ = q ∧ T + 1 = 2 * q ∧ C ≤ T) ∧
      (2 * q ≤ T ∧ T ≤ 2 * q + 2 ∨ T + 1 = 2 * q) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : n - 2 + 2 = n := by omega
  have hprod : q * (n - 2) + 2 * q = q * n := by
    calc
      _ = q * (n - 2 + 2) := by ring
      _ = q * n := by rw [hN]
  have hCR : (C : ℝ) < ((2 * q + 2 : ℕ) : ℝ) := by
    push_cast
    linarith only [hqu, hC]
  have hCup : C ≤ 2 * q + 1 := by
    have ht : C < 2 * q + 2 := by exact_mod_cast hCR
    omega
  have hmR : (m : ℝ) = (q : ℝ) * n + s := by exact_mod_cast hm
  by_cases hCe : C % 2 = 0
  · by_cases hhalf : μ < (q : ℝ) + 1 / 2
    · have hCR' : (C : ℝ) < ((2 * q + 1 : ℕ) : ℝ) := by
        push_cast
        linarith only [hC, hhalf]
      have hC' : C ≤ 2 * q := by
        have ht : C < 2 * q + 1 := by exact_mod_cast hCR'
        omega
      refine ⟨2 * q, hC', ?_, ?_, Or.inl ?_, Or.inl ⟨by omega, by omega⟩⟩
      · rw [Nat.even_iff]
        omega
      · omega
      · push_cast
        linarith only [hhalf]
    · have hhalf' : (q : ℝ) + 1 / 2 ≤ μ := le_of_not_gt hhalf
      have hmhalf := mul_le_mul_of_nonneg_right hhalf' (show (0 : ℝ) ≤ n by positivity)
      have hsR : (2 : ℝ) ≤ s := by nlinarith only [hmhalf, hμ, hmR, hnR]
      have hs : 2 ≤ s := by exact_mod_cast hsR
      refine ⟨2 * q + 2, by omega, ?_, ?_, Or.inl ?_, Or.inl ⟨by omega, by omega⟩⟩
      · rw [Nat.even_iff]
        omega
      · omega
      · push_cast
        linarith only [hqu]
  · have hCo : C % 2 = 1 := by omega
    by_cases hs : s = 0
    · have hμq : μ = q := by
        apply mul_right_cancel₀ (show (n : ℝ) ≠ 0 by positivity)
        rw [hμ, hmR, hs, Nat.cast_zero, add_zero]
      have hC' : C ≤ 2 * q - 1 := by
        have ht : C ≤ 2 * q := by
          have htR : (C : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by simpa only [hμq, Nat.cast_mul, Nat.cast_ofNat] using hC
          exact_mod_cast htR
        omega
      refine ⟨2 * q - 1, hC', ?_, ?_, Or.inr ⟨hμq, by omega, hC'⟩, Or.inr (by omega)⟩
      · rw [Nat.even_iff]
        omega
      · omega
    · refine ⟨2 * q + 1, hCup, ?_, ?_, Or.inl ?_, Or.inl ⟨by omega, by omega⟩⟩
      · rw [Nat.even_iff]
        omega
      · omega
      · push_cast
        linarith only [hqu]

end ResearchMain.Chores
