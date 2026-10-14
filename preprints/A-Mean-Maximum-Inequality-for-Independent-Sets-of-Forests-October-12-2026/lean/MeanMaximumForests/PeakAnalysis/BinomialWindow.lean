import MeanMaximumForests.PeakAnalysis.BinomialLog

namespace MeanMaximumForests.PeakAnalysis

/-- Adjacent binomial log masses vary by `O(1/r)` throughout a fixed-width central window. -/
theorem binomial_central_log_step (n k : ℕ) (z r L : ℝ)
    (hz : (1 / 4 : ℝ) ≤ z) (hz1 : z ≤ 1) (hL : 0 ≤ L)
    (hr : 40 * (L + 1) ≤ r) (hrn : r ^ 2 = n)
    (hwindow : |(k : ℝ) - z * n / (1 + z)| ≤ L * r) :
    k < n ∧ r * |Real.log (binomialSizeMass n z (k + 1)) -
      Real.log (binomialSizeMass n z k)| ≤ 60 * (L + 1) := by
  let m := z * n / (1 + z)
  have hz0 : 0 < z := by linarith
  have hzden : 0 < 1 + z := by linarith
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hn0 : (0 : ℝ) < n := by nlinarith only [hrn, sq_pos_of_pos hr0]
  have hmeq : (1 + z) * m = z * n := by dsimp [m]; field_simp
  have hmlo : (n : ℝ) / 5 ≤ m := by
    have h := mul_nonneg hn0.le (by linarith : 0 ≤ 4 * z - 1)
    dsimp [m]
    apply (le_div_iff₀ hzden).mpr
    nlinarith only [h]
  have hmhi : m ≤ (n : ℝ) / 2 := by
    have h := mul_nonneg hn0.le (sub_nonneg.mpr hz1)
    dsimp [m]
    apply (div_le_iff₀ hzden).mpr
    nlinarith only [h]
  have hwidth : L * r ≤ (n : ℝ) / 40 := by
    have h := mul_le_mul_of_nonneg_right hr hr0.le
    nlinarith only [h, hrn, hr0.le]
  have hkl := (abs_le.mp hwindow).1
  have hku := (abs_le.mp hwindow).2
  change - (L * r) ≤ (k : ℝ) - m at hkl
  change (k : ℝ) - m ≤ L * r at hku
  have hkn : (k : ℝ) < n := by linarith
  have hkn' : k < n := by exact_mod_cast hkn
  have hdk : (n : ℝ) / 20 ≤ k + 1 := by linarith
  have hnk : (n : ℝ) / 4 ≤ (n : ℝ) - k := by linarith
  have hdz : (n : ℝ) / 20 ≤ z * ((n : ℝ) - k) := by
    have h := mul_nonneg (by linarith : 0 ≤ z - 1 / 4) (by linarith : 0 ≤ (n : ℝ) - k)
    nlinarith only [h, hnk, hn0.le]
  have hs := binomial_log_step_scaled n k z ((n : ℝ) / 20) hz0 hkn' (by positivity) hdk hdz
  have he : z * ((n : ℝ) - k) - (k + 1) = (1 + z) * (m - k) - 1 := by
    nlinarith only [hmeq]
  rw [he] at hs
  have habs : |(1 + z) * (m - k) - 1| ≤ (1 + z) * |m - k| + 1 := by
    have h := abs_add_le ((1 + z) * (m - k)) (-1)
    simpa only [sub_eq_add_neg, abs_mul, abs_of_pos hzden, abs_neg, abs_one] using h
  have hw : |m - k| ≤ L * r := by simpa only [abs_sub_comm] using hwindow
  have hm := mul_le_mul (by linarith : 1 + z ≤ 2) hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have hscaled : r ^ 2 * |Real.log (binomialSizeMass n z (k + 1)) -
      Real.log (binomialSizeMass n z k)| ≤ 20 * (2 * L * r + 1) := by
    rw [hrn]
    nlinarith only [hs, habs, hm]
  refine ⟨hkn', ?_⟩
  apply (mul_le_mul_iff_left₀ hr0).mp
  nlinarith only [hscaled, hr1, mul_nonneg hL hr0.le]

/-- A finite telescoping estimate, with the scale kept outside the absolute values. -/
theorem nat_scaled_log_lipschitz (f : ℕ → ℝ) (a b : ℕ) (r B : ℝ) (hab : a ≤ b) (hr : 0 ≤ r)
    (hs : ∀ k, a ≤ k → k < b → r * |f (k + 1) - f k| ≤ B) :
    r * |f b - f a| ≤ B * ((b : ℝ) - a) := by
  have aux : ∀ j : ℕ, a + j ≤ b → r * |f (a + j) - f a| ≤ B * j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hp := ih (by omega)
      have hstep := hs (a + j) (by omega) (by omega)
      simp only [Nat.add_assoc] at hstep
      have htriangle := abs_sub_le (f (a + (j + 1))) (f (a + j)) (f a)
      have hm := mul_le_mul_of_nonneg_left htriangle hr
      simp only [Nat.cast_add, Nat.cast_one] at hp hstep ⊢
      nlinarith only [hp, hstep, hm]
  have h := aux (b - a) (by omega)
  rw [Nat.add_sub_of_le hab, Nat.cast_sub hab] at h
  exact h

end MeanMaximumForests.PeakAnalysis
