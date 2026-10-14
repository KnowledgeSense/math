import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset
namespace SumsetRanges

/-- A telescoping estimate for a change in the upper binomial parameter. -/
theorem choose_le_choose_add_gap (n c d : ℕ) (hnc : n ≤ c) (hd : 1 ≤ d) :
    c.choose d ≤ n.choose d + (c - n) * c.choose (d - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnc
  simp only [Nat.add_sub_cancel_left]
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (Nat.le_add_right n k)
    have hm := Nat.choose_le_succ (n + k) (d - 1)
    have hm' := Nat.mul_le_mul_left (k + 1) hm
    rw [Nat.add_succ, Nat.choose_succ_left _ _ hd]
    nlinarith

/-- Removing at most a `1 / (4h)` fraction loses at most half of each low coefficient. -/
theorem choose_le_twice_choose (h c n d : ℕ) (_hh : 1 ≤ h) (hc : 2 * h ≤ c)
    (hn : n ≤ c) (hgap : 4 * h * (c - n) ≤ c) (hd : d ≤ h) :
    c.choose d ≤ 2 * n.choose d := by
  by_cases hd0 : d = 0
  · simp [hd0]
  have hdp : 1 ≤ d := Nat.pos_of_ne_zero hd0
  have hdc : d - 1 ≤ c := by omega
  have hsub := Nat.sub_add_cancel hdc
  have hpred : d - 1 + 1 = d := by omega
  have hratio := Nat.choose_succ_right_eq c (d - 1)
  rw [hpred] at hratio
  have hdt := Nat.mul_le_mul_right (c - n) hd
  have hsmall : 2 * d * (c - n) ≤ c - (d - 1) := by nlinarith
  have hmul := Nat.mul_le_mul_right (c.choose (d - 1)) hsmall
  have hloss : 2 * (c - n) * c.choose (d - 1) ≤ c.choose d := by
    apply Nat.le_of_mul_le_mul_left (c := d) _ hdp
    nlinarith [hratio]
  have htel := choose_le_choose_add_gap n c d hn hdp
  nlinarith

/-- Successive small binomial coefficients grow by a factor of at least two. -/
theorem twice_choose_le_choose_succ (c k : ℕ) (hk : 3 * k + 2 ≤ c) :
    2 * c.choose k ≤ c.choose (k + 1) := by
  have hkc : k ≤ c := by omega
  have hsub := Nat.sub_add_cancel hkc
  have hratio := Nat.choose_succ_right_eq c k
  have hsmall : 2 * (k + 1) ≤ c - k := by omega
  have hmul := Nat.mul_le_mul_right (c.choose k) hsmall
  apply Nat.le_of_mul_le_mul_right (c := k + 1) _ (by omega)
  nlinarith

/-- A finite geometric estimate for the initial binomial coefficients. -/
theorem sum_range_choose_le_twice (c k : ℕ) (hk : 3 * k ≤ c) :
    (∑ j ∈ range (k + 1), c.choose j) ≤ 2 * c.choose k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hbound := twice_choose_le_choose_succ c k (by omega)
    have hprev := ih (by omega)
    rw [sum_range_succ]
    omega

/-- Reversing the indices in a binomial tail. -/
theorem sum_Icc_choose_sub_eq (c D : ℕ) (hD : 1 ≤ D) :
    (∑ e ∈ Icc 2 D, c.choose (D - e)) = ∑ j ∈ range (D - 1), c.choose j := by
  refine sum_bij (fun e _ => D - e) ?_ ?_ ?_ ?_
  · intro e he
    simp only [mem_Icc] at he
    simp only [mem_range]
    omega
  · intro e he f hf hef
    simp only [mem_Icc] at he hf
    omega
  · intro j hj
    simp only [mem_range] at hj
    refine ⟨D - j, ?_, ?_⟩
    · simp only [mem_Icc]
      omega
    · omega
  · intro e he
    rfl

/-- The tail beginning two degrees below the top, with its exact natural-number scale. -/
theorem choose_tail_le_scaled_previous (h c D : ℕ) (hc : 4 * h ≤ c)
    (hD : 1 ≤ D) (hDh : D ≤ h) :
    c * (∑ e ∈ Icc 2 D, c.choose (D - e)) ≤ 4 * h * c.choose (D - 1) := by
  by_cases hD1 : D = 1
  · simp [hD1]
  have hD2 : 2 ≤ D := by omega
  rw [sum_Icc_choose_sub_eq c D hD]
  have hindex : D - 2 + 1 = D - 1 := by omega
  have hsum := sum_range_choose_le_twice c (D - 2) (by omega)
  rw [hindex] at hsum
  have hratio := Nat.choose_succ_right_eq c (D - 2)
  rw [hindex] at hratio
  have hdc : D - 2 ≤ c := by omega
  have hsub := Nat.sub_add_cancel hdc
  have hsmall : c ≤ 2 * (c - (D - 2)) := by omega
  have hmul := Nat.mul_le_mul_right (c.choose (D - 2)) hsmall
  have hdegree := Nat.mul_le_mul_right (c.choose (D - 1)) (show D - 1 ≤ h by omega)
  have hstep : c * c.choose (D - 2) ≤ 2 * h * c.choose (D - 1) := by
    nlinarith
  have hsum' := Nat.mul_le_mul_left c hsum
  nlinarith

/-- The same tail is bounded by twice its largest coefficient. -/
theorem choose_tail_le_twice_top (h c : ℕ) (hh : 2 ≤ h) (hc : 4 * h ≤ c) :
    (∑ e ∈ Icc 2 h, c.choose (h - e)) ≤ 2 * c.choose (h - 2) := by
  rw [sum_Icc_choose_sub_eq c h (by omega)]
  have hi : h - 2 + 1 = h - 1 := by omega
  simpa only [hi] using sum_range_choose_le_twice c (h - 2) (by omega)

end SumsetRanges
