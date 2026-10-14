import TerminalLogConcavity.ModelCoefficients

namespace TerminalLogConcavity

theorem choose_previous_le {q j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ q) :
    q.choose (j - 1) ≤ q * q.choose j := by
  have h := Nat.choose_succ_right_eq q (j - 1)
  have he : j - 1 + 1 = j := by omega
  rw [he] at h
  have hdiff : 1 ≤ q - (j - 1) := by omega
  have hlow := Nat.mul_le_mul_left (q.choose (j - 1)) hdiff
  have hhigh := Nat.mul_le_mul_right (q.choose j) hjq
  nlinarith

theorem modelCoefficient_previous {q K D j : ℕ} {a : ℝ}
    (ha : 1 ≤ a) (hj : 1 ≤ j) (hjq : j ≤ q) :
    a ^ D * modelCoefficient q K D a (j - 1) ≤
      (q : ℝ) * modelCoefficient q K D a j := by
  have hc : (q.choose (j - 1) : ℝ) ≤ (q : ℝ) * q.choose j := by
    exact_mod_cast choose_previous_le hj hjq
  have hjid : j - 1 + 1 = j := by omega
  have hexp : D + (K + D * (j - 1) + (j - 1) ^ 2) ≤ K + D * j + j ^ 2 := by
    nlinarith
  have hp := pow_le_pow_right₀ ha hexp
  have hm := mul_le_mul hc hp (by positivity) (by positivity)
  unfold modelCoefficient
  calc
    _ = (q.choose (j - 1) : ℝ) * a ^ (D + (K + D * (j - 1) + (j - 1) ^ 2)) := by
      rw [pow_add]; ring
    _ ≤ _ := by convert hm using 1 ; ring

theorem modelCoefficient_ratio {q K D j : ℕ} {a : ℝ}
    (ha : 1 ≤ a) (hj : 1 ≤ j) (hjq : j ≤ q) :
    modelCoefficient q K D a (j - 1) ≤
      ((q : ℝ) / a ^ D) * modelCoefficient q K D a j := by
  have h := modelCoefficient_previous (K := K) (D := D) ha hj hjq
  have ha0 : 0 < a ^ D := by positivity
  have hh : modelCoefficient q K D a (j - 1) ≤
      ((q : ℝ) * modelCoefficient q K D a j) / a ^ D :=
    (le_div_iff₀ ha0).mpr (by simpa [mul_comm] using h)
  convert hh using 1 ; ring

theorem modelCoefficient_backwards {q K D j k : ℕ} {a : ℝ}
    (ha : 1 ≤ a) (hjq : j ≤ q) (hk : k ≤ j) :
    modelCoefficient q K D a (j - k) ≤
      ((q : ℝ) / a ^ D) ^ k * modelCoefficient q K D a j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ j := by omega
    have hs := modelCoefficient_ratio (K := K) (D := D) ha
      (by omega : 1 ≤ j - k) (by omega : j - k ≤ q)
    have hi := mul_le_mul_of_nonneg_left (ih hk')
      (by positivity : 0 ≤ (q : ℝ) / a ^ D)
    have he : j - (k + 1) = (j - k) - 1 := by omega
    rw [he]
    calc
      _ ≤ ((q : ℝ) / a ^ D) * modelCoefficient q K D a (j - k) := hs
      _ ≤ ((q : ℝ) / a ^ D) * (((q : ℝ) / a ^ D) ^ k * modelCoefficient q K D a j) := hi
      _ = _ := by rw [pow_succ]; ring

end TerminalLogConcavity
