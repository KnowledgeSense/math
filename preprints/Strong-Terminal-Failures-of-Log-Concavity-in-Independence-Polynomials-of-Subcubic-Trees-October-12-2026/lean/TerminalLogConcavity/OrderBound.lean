import TerminalLogConcavity.Parameters

namespace TerminalLogConcavity

theorem successor_le_two_power (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih => rw [pow_succ]; omega

theorem target_power_bound {q H h : ℕ} (hq : 2 ≤ q) (hH : H ≤ 2 ^ h) :
    target q H ≤ 2 ^ (8 * q + h) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hq
  have hqpow : (2 + k) ^ 4 ≤ 2 ^ (4 * (k + 1)) := by
    have h := Nat.pow_le_pow_left (successor_le_two_power (k + 1)) 4
    convert h using 1 <;> ring
  unfold target
  calc
    2 ^ (2 + k + 10) * (2 + k) ^ 4 * H ≤
        2 ^ (2 + k + 10) * 2 ^ (4 * (k + 1)) * 2 ^ h :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hqpow) hH
    _ = 2 ^ ((2 + k + 10) + 4 * (k + 1) + h) := by rw [← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

theorem amplifier_width_bound {q H h : ℕ} (hq : 2 ≤ q) (hHpos : 1 ≤ H)
    (hH : H ≤ 2 ^ h) :
    2 ^ thresholdIndex (target q H) ≤ 16 * q + 2 * h := by
  have ht := thresholdIndex_pos (target_gt_one (by omega : 1 ≤ q) hHpos)
  obtain ⟨t, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  have hg : 2 ^ (2 ^ thresholdIndex (target q H)) ≤ selectedAmplifier q H := by
    unfold selectedAmplifier
    rw [he]
    exact amplifier_growth t
  have ha := (selectedAmplifier_bounds (by omega : 1 ≤ q) hHpos).2
  have hQ := Nat.pow_le_pow_left (target_power_bound hq hH) 2
  have hb : (2 ^ (8 * q + h)) ^ 2 = 2 ^ (16 * q + 2 * h) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [hb] at hQ
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hg.trans (ha.trans hQ))

theorem order_bound_from_block_sum {q H h S N : ℕ} (hq : 2 ≤ q) (hHpos : 1 ≤ H)
    (hH : H ≤ 2 ^ h) (hS : S < 16 * q ^ 4)
    (hN : N < 4 * 2 ^ thresholdIndex (target q H) * S) :
    N ≤ 1200 * q ^ 4 * (q + h) := by
  have hw := amplifier_width_bound hq hHpos hH
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hw) (Nat.le_of_lt hS)
  have : (4 * (16 * q + 2 * h)) * (16 * q ^ 4) ≤
      1200 * q ^ 4 * (q + h) := by nlinarith
  exact (Nat.le_of_lt hN).trans (hmul.trans this)

end TerminalLogConcavity
