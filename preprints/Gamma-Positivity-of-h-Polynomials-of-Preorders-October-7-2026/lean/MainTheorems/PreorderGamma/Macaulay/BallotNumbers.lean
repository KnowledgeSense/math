import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace ResearchMain.PreorderGamma.Macaulay

def ballotNumber (n r : ℕ) : ℕ := if r = 0 then 1 else n.choose r - n.choose (r - 1)

@[simp] theorem ballotNumber_zero (n : ℕ) : ballotNumber n 0 = 1 := rfl

@[simp] theorem ballotNumber_succ (n r : ℕ) :
    ballotNumber n (r + 1) = n.choose (r + 1) - n.choose r := by
  simp [ballotNumber]

theorem choose_next_le_of_upper_half {n r : ℕ} (h : n ≤ 2 * r + 1) :
    n.choose (r + 1) ≤ n.choose r := by
  apply Nat.le_of_mul_le_mul_right (c := r + 1) _ (by omega)
  rw [Nat.choose_succ_right_eq]
  exact Nat.mul_le_mul_left _ (by omega : n - r ≤ r + 1)

theorem choose_le_next_of_lower_half {n r : ℕ} (h : 2 * r + 1 ≤ n) :
    n.choose r ≤ n.choose (r + 1) := by
  apply Nat.le_of_mul_le_mul_right (c := r + 1) _ (by omega)
  rw [Nat.choose_succ_right_eq]
  exact Nat.mul_le_mul_left _ (by omega : r + 1 ≤ n - r)

theorem ballotNumber_eq_zero_of_large {n r : ℕ} (h : n < 2 * r) : ballotNumber n r = 0 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  rw [ballotNumber_succ]
  exact Nat.sub_eq_zero_of_le (choose_next_le_of_upper_half (by omega))

@[simp] theorem ballotNumber_empty (r : ℕ) : ballotNumber 0 r = if r = 0 then 1 else 0 := by
  cases r with
  | zero => rfl
  | succ r => simp [ballotNumber_succ]

theorem ballotNumber_step (n r : ℕ) :
    ballotNumber (n + 1) (r + 1) = ballotNumber n (r + 1) +
      if 2 * (r + 1) ≤ n + 1 then ballotNumber n r else 0 := by
  by_cases hcap : 2 * (r + 1) ≤ n + 1
  · rw [ite_eq_left hcap]
    cases r with
    | zero =>
      simp only [ballotNumber_succ, ballotNumber_zero, Nat.zero_add,
        Nat.choose_one_right, Nat.choose_zero_right]
      omega
    | succ s =>
      have h₁ : n.choose (s + 1) ≤ n.choose (s + 1 + 1) :=
        choose_le_next_of_lower_half (by omega)
      have h₂ : n.choose s ≤ n.choose (s + 1) :=
        choose_le_next_of_lower_half (by omega)
      simp only [ballotNumber_succ, Nat.choose_succ_succ']
      omega
  · rw [ite_eq_right hcap,
      ballotNumber_eq_zero_of_large (by omega : n + 1 < 2 * (r + 1)),
      ballotNumber_eq_zero_of_large (by omega : n < 2 * (r + 1)), Nat.add_zero]

end ResearchMain.PreorderGamma.Macaulay
