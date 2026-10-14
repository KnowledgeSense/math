import MeanMaximumForests.PeakAnalysis.BinomialWindow

namespace MeanMaximumForests.PeakAnalysis

theorem binomial_central_log_comparison (n j k : ℕ) (z r L : ℝ)
    (hz : (1 / 4 : ℝ) ≤ z) (hz1 : z ≤ 1) (hL : 0 ≤ L)
    (hr : 40 * (L + 1) ≤ r) (hrn : r ^ 2 = n)
    (hj : |(j : ℝ) - z * n / (1 + z)| ≤ L * r)
    (hk : |(k : ℝ) - z * n / (1 + z)| ≤ L * r) :
    |Real.log (binomialSizeMass n z j) - Real.log (binomialSizeMass n z k)| ≤
      120 * L * (L + 1) := by
  have hr0 : 0 < r := by linarith
  wlog hjk : j ≤ k generalizing j k
  · have h := this k j hk hj (by omega)
    simpa only [abs_sub_comm] using h
  have hs (i : ℕ) (hji : j ≤ i) (hik : i < k) :
      r * |Real.log (binomialSizeMass n z (i + 1)) - Real.log (binomialSizeMass n z i)| ≤
        60 * (L + 1) := by
    have hji' : (j : ℝ) ≤ i := by exact_mod_cast hji
    have hik' : (i : ℝ) ≤ k := by exact_mod_cast hik.le
    have hi : |(i : ℝ) - z * n / (1 + z)| ≤ L * r := by
      rw [abs_le] at hj hk ⊢
      constructor <;> linarith [hj.1, hk.2]
    exact (binomial_central_log_step n i z r L hz hz1 hL hr hrn hi).2
  have hb := nat_scaled_log_lipschitz (fun i => Real.log (binomialSizeMass n z i)) j k r
    (60 * (L + 1)) hjk hr0.le hs
  have hspan : (k : ℝ) - j ≤ 2 * L * r := by
    have h1 := (abs_le.mp hj).1
    have h2 := (abs_le.mp hk).2
    linarith
  have hm := mul_le_mul_of_nonneg_left hspan (by positivity : 0 ≤ 60 * (L + 1))
  apply (mul_le_mul_iff_right₀ hr0).mp
  rw [abs_sub_comm]
  nlinarith only [hb, hm]

/-- All binomial masses in a fixed central window are uniformly comparable. -/
theorem binomial_central_mass_comparison (n j k : ℕ) (z r L : ℝ)
    (hz : (1 / 4 : ℝ) ≤ z) (hz1 : z ≤ 1) (hL : 0 ≤ L)
    (hr : 40 * (L + 1) ≤ r) (hrn : r ^ 2 = n)
    (hj : |(j : ℝ) - z * n / (1 + z)| ≤ L * r)
    (hk : |(k : ℝ) - z * n / (1 + z)| ≤ L * r) :
    Real.exp (-(120 * L * (L + 1))) * binomialSizeMass n z k ≤ binomialSizeMass n z j := by
  have h := binomial_central_log_comparison n j k z r L hz hz1 hL hr hrn hj hk
  have hjn := (binomial_central_log_step n j z r L hz hz1 hL hr hrn hj).1
  have hkn := (binomial_central_log_step n k z r L hz hz1 hL hr hrn hk).1
  have hz0 : 0 < z := by linarith
  have hjpos := binomialSizeMass_pos n j z hz0 hjn.le
  have hkpos := binomialSizeMass_pos n k z hz0 hkn.le
  have hl : -(120 * L * (L + 1)) + Real.log (binomialSizeMass n z k) ≤
      Real.log (binomialSizeMass n z j) := by linarith [(abs_le.mp h).1]
  have he := Real.exp_le_exp.mpr hl
  rwa [Real.exp_add, Real.exp_log hkpos, Real.exp_log hjpos] at he

end MeanMaximumForests.PeakAnalysis
