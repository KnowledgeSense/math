import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp

namespace TerminalLogConcavity

theorem power_le_choose_times_power {q j : ℕ} (hj : j ≤ q) :
    q ^ j ≤ j ^ j * q.choose j := by
  induction j generalizing q with
  | zero => simp
  | succ j ih =>
    cases q with
    | zero => omega
    | succ q =>
      by_cases hz : j = 0
      · subst j; simp
      · have hjpos : 0 < j := by omega
        have hqj : j ≤ q := by omega
        have h := ih hqj
        have hr : (q + 1) * j ≤ q * (j + 1) := by nlinarith
        have hp := Nat.pow_le_pow_left hr j
        rw [mul_pow, mul_pow] at hp
        have hm := Nat.mul_le_mul_right ((j + 1) ^ j) h
        have hcombined : j ^ j * (q + 1) ^ j ≤
            j ^ j * ((j + 1) ^ j * q.choose j) := by nlinarith
        have hc := Nat.le_of_mul_le_mul_left hcombined (by positivity)
        have hm' := Nat.mul_le_mul_left (q + 1) hc
        have he := Nat.add_one_mul_choose_eq q j
        calc
          (q + 1) ^ (j + 1) = (q + 1) * (q + 1) ^ j := by rw [pow_succ]; ring
          _ ≤ (q + 1) * ((j + 1) ^ j * q.choose j) := hm'
          _ = (j + 1) ^ (j + 1) * (q + 1).choose (j + 1) := by
            calc
              _ = (j + 1) ^ j * ((q + 1) * q.choose j) := by ring
              _ = _ := by rw [he, pow_succ]; ring

theorem successor_power_le_three {n : ℕ} (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℝ) ^ n ≤ 3 * (n : ℝ) ^ n := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hbase : 1 + 1 / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
    simpa [add_comm] using Real.add_one_le_exp (1 / (n : ℝ))
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 1 / (n : ℝ)) hbase n
  rw [← Real.exp_nat_mul] at hpow
  have he : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
  rw [he] at hpow
  have hbound := mul_le_mul_of_nonneg_right (hpow.trans (le_of_lt Real.exp_one_lt_three))
    (by positivity : 0 ≤ (n : ℝ) ^ n)
  rw [← mul_pow] at hbound
  have hmul : (1 + 1 / (n : ℝ)) * (n : ℝ) = (n + 1 : ℕ) := by
    push_cast
    field_simp
  rwa [hmul] at hbound

theorem factorial_power_bound (n : ℕ) : n ^ n ≤ 3 ^ n * n.factorial := by
  have hreal : (n : ℝ) ^ n ≤ (3 : ℝ) ^ n * (n.factorial : ℝ) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      by_cases hn : n = 0
      · subst n; norm_num
      · have hp := successor_power_le_three (by omega : 1 ≤ n)
        calc
          ((n + 1 : ℕ) : ℝ) ^ (n + 1) = (n + 1 : ℕ) * ((n + 1 : ℕ) : ℝ) ^ n := by ring
          _ ≤ (n + 1 : ℕ) * (3 * (n : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left hp (by positivity)
          _ ≤ (n + 1 : ℕ) * (3 * ((3 : ℝ) ^ n * (n.factorial : ℝ))) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ih (by norm_num)) (by positivity)
          _ = (3 : ℝ) ^ (n + 1) * ((n + 1).factorial : ℝ) := by
            rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
            ring
  exact_mod_cast hreal

theorem choose_dilated_bound {q j : ℕ} (hj : j ≤ q) (k : ℕ) :
    (k * q).choose j ≤ (3 * k) ^ j * q.choose j := by
  have hu := Nat.descFactorial_le_pow (k * q) j
  rw [Nat.descFactorial_eq_factorial_mul_choose, mul_pow] at hu
  have hl := power_le_choose_times_power hj
  have hf := factorial_power_bound j
  have h1 := Nat.mul_le_mul_left (k ^ j) hl
  have h2 := Nat.mul_le_mul_left (k ^ j) (Nat.mul_le_mul_right (q.choose j) hf)
  have htotal : j.factorial * (k * q).choose j ≤
      j.factorial * ((3 * k) ^ j * q.choose j) := by
    rw [mul_pow]
    nlinarith
  exact Nat.le_of_mul_le_mul_left htotal (Nat.factorial_pos j)

end TerminalLogConcavity
