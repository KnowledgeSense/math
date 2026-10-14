import MainTheorems.Corona.Logarithms
import Mathlib.Algebra.Order.Floor.Ring

namespace ResearchMain.Corona

noncomputable def balanceRatio (q : ℝ) : ℝ := Real.log (1 + 2 / q) / Real.log (1 + 1 / q)
noncomputable def balanceIndex (q : ℝ) (m : ℕ) : ℕ := ⌊balanceRatio q * m⌋₊
noncomputable def separationRate (q : ℝ) : ℝ := balanceRatio q / (q + 1) - 2 / (q + 2)

theorem balanceRatio_bounds {q : ℝ} (hq : 0 < q) : 1 < balanceRatio q ∧ balanceRatio q < 2 := by
  have hu : 1 < 1 + 1 / q := by
    have h : (0 : ℝ) < 1 / q := by positivity
    linarith
  have hv : 0 < 1 + 2 / q := by positivity
  have hlog : 0 < Real.log (1 + 1 / q) := Real.log_pos hu
  constructor
  · rw [balanceRatio, lt_div_iff₀ hlog, one_mul]
    apply Real.log_lt_log (by linarith)
    have h := (div_lt_div_iff_of_pos_right hq).mpr (by norm_num : (1 : ℝ) < 2)
    linarith
  · rw [balanceRatio, div_lt_iff₀ hlog]
    have hinv : (0 : ℝ) < 1 / q := by positivity
    have hsq : 1 + 2 / q < (1 + 1 / q) ^ 2 := by
      rw [show (2 : ℝ) / q = 2 * (1 / q) by ring]
      nlinarith [sq_pos_of_pos hinv]
    have h := Real.log_lt_log hv hsq
    rw [Real.log_pow] at h
    norm_num at h
    simpa only [one_div] using h

theorem separationRate_positive {q : ℝ} (hq : 0 < q) : 0 < separationRate q :=
  balance_separation hq

theorem balanceIndex_floor_bounds {q : ℝ} (hq : 0 < q) (m : ℕ) :
    (balanceIndex q m : ℝ) ≤ balanceRatio q * m ∧
      balanceRatio q * m < balanceIndex q m + 1 := by
  have hnonneg : 0 ≤ balanceRatio q * m :=
    mul_nonneg (by have := (balanceRatio_bounds hq).1; linarith) (Nat.cast_nonneg m)
  exact ⟨Nat.floor_le hnonneg, Nat.lt_floor_add_one _⟩

theorem balanceIndex_order {q : ℝ} (hq : 0 < q) {m : ℕ} (hm : 1 ≤ m) :
    m ≤ balanceIndex q m ∧ balanceIndex q m < 2 * m := by
  have hb := balanceRatio_bounds hq
  have hf := balanceIndex_floor_bounds hq m
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  constructor
  · have h : (m : ℝ) ≤ balanceRatio q * m := by nlinarith only [hb.1, hm0]
    exact (Nat.le_floor_iff (by nlinarith only [hb.1, hm0] : 0 ≤ balanceRatio q * m)).mpr h
  · have h : (balanceIndex q m : ℝ) < 2 * m := by nlinarith only [hf.1, hb.2, hm0]
    exact_mod_cast h

theorem balanceIndex_powers {q : ℝ} (hq : 0 < q) (m : ℕ) :
    (1 + 1 / q) ^ balanceIndex q m ≤ (1 + 2 / q) ^ m ∧
      (1 + 2 / q) ^ m < (1 + 1 / q) ^ (balanceIndex q m + 1) := by
  have hu : 1 < 1 + 1 / q := by
    have h : (0 : ℝ) < 1 / q := by positivity
    linarith
  have hv : 0 < 1 + 2 / q := by positivity
  have hlog : 0 < Real.log (1 + 1 / q) := Real.log_pos hu
  have hf := balanceIndex_floor_bounds hq m
  have he : balanceRatio q * m * Real.log (1 + 1 / q) = m * Real.log (1 + 2 / q) := by
    unfold balanceRatio
    calc
      _ = Real.log (1 + 2 / q) *
          (Real.log (1 + 1 / q) / Real.log (1 + 1 / q)) * m := by ring
      _ = _ := by rw [div_self (ne_of_gt hlog)]; ring
  constructor
  · apply (Real.log_le_log_iff (pow_pos (by linarith) _) (pow_pos hv _)).mp
    rw [Real.log_pow, Real.log_pow]
    have h := mul_le_mul_of_nonneg_right hf.1 hlog.le
    rw [he] at h
    exact h
  · apply (Real.log_lt_log_iff (pow_pos hv _) (pow_pos (by linarith) _)).mp
    rw [Real.log_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
    have h := mul_lt_mul_of_pos_right hf.2 hlog
    rw [he] at h
    exact h

theorem balanceIndex_separation {q : ℝ} (hq : 0 < q) (m : ℕ) :
    separationRate q * m - 1 / (q + 1) <
      (balanceIndex q m : ℝ) / (q + 1) - 2 * m / (q + 2) := by
  have hf := (balanceIndex_floor_bounds hq m).2
  have hq1 : 0 < q + 1 := by linarith
  have h := (div_lt_div_iff_of_pos_right hq1).mpr (show balanceRatio q * m - 1 < balanceIndex q m by linarith)
  unfold separationRate
  calc
    _ = (balanceRatio q * m - 1) / (q + 1) - 2 * m / (q + 2) := by ring
    _ < _ := sub_lt_sub_right h _

end ResearchMain.Corona
