import MeanMaximumForests.PeakAnalysis.BinomialLocalBounds
import MeanMaximumForests.PeakAnalysis.BinomialVariation
import Mathlib.Data.Nat.Choose.Vandermonde

namespace MeanMaximumForests.PeakAnalysis
open Finset

noncomputable def binomialIntegerMass (n : ℕ) (z : ℝ) (k : ℤ) : ℝ :=
  if 0 ≤ k then binomialSizeMass n z k.toNat else 0

@[simp] theorem binomialIntegerMass_natCast (n k : ℕ) (z : ℝ) :
    binomialIntegerMass n z (k : ℤ) = binomialSizeMass n z k := by simp [binomialIntegerMass]

theorem binomialIntegerMass_negative (n : ℕ) (z : ℝ) {k : ℤ} (hk : k < 0) :
    binomialIntegerMass n z k = 0 := by simp [binomialIntegerMass, not_le.mpr hk]

theorem binomialIntegerMass_above (n : ℕ) (z : ℝ) {k : ℤ} (hk : (n : ℤ) < k) :
    binomialIntegerMass n z k = 0 := by
  have hk0 : 0 ≤ k := by omega
  have hkn : n < k.toNat := by omega
  simp only [binomialIntegerMass, hk0, ↓reduceIte, binomialSizeMass_eq_zero z hkn]

theorem binomialIntegerMass_nonneg (n : ℕ) (z : ℝ) (hz : 0 < z) (k : ℤ) :
    0 ≤ binomialIntegerMass n z k := by
  unfold binomialIntegerMass binomialSizeMass
  split_ifs <;> positivity

/-- Vandermonde's identity, including the exact normalization of the probability masses. -/
theorem binomial_convolution_nat (m n k : ℕ) (z : ℝ) :
    binomialSizeMass (m + n) z k =
      ∑ i ∈ range (k + 1), binomialSizeMass m z i * binomialSizeMass n z (k - i) := by
  have hc : ((m + n).choose k : ℝ) =
      ∑ i ∈ range (k + 1), (m.choose i : ℝ) * n.choose (k - i) := by
    rw [Nat.add_choose_eq, Nat.cast_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Nat.cast_mul]
  unfold binomialSizeMass
  rw [hc, sum_mul, sum_div]
  apply sum_congr rfl
  intro i hi
  have hik : i ≤ k := by have := mem_range.mp hi; omega
  rw [div_mul_div_comm, ← pow_add]
  have hp : z ^ k = z ^ i * z ^ (k - i) := by rw [← pow_add, Nat.add_sub_of_le hik]
  rw [hp]
  ring

/-- Central binomial lower bounds also hold for integer indices; being central forces the index into the support. -/
theorem binomialIntegerMass_central_lower (n : ℕ) (k : ℤ) (z r L : ℝ)
    (hz : (1 / 4 : ℝ) ≤ z) (hz1 : z ≤ 1) (hL : 1 ≤ L)
    (hr : 40 * (L + 1) ≤ r) (hrn : r ^ 2 = n)
    (hk : |(k : ℝ) - z * n / (1 + z)| ≤ L * r) :
    Real.exp (-(120 * L * (L + 1))) ≤ 6 * r * binomialIntegerMass n z k := by
  have hr0 : 0 < r := by linarith
  have hzden : 0 < 1 + z := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hmlo : (n : ℝ) / 5 ≤ z * n / (1 + z) := by
    apply (le_div_iff₀ hzden).mpr
    have h := mul_nonneg hn0 (by linarith : 0 ≤ 4 * z - 1)
    nlinarith only [h]
  have hwidth : L * r ≤ (n : ℝ) / 40 := by
    have h := mul_le_mul_of_nonneg_right hr hr0.le
    nlinarith only [h, hrn, hr0.le]
  have hk0 : (0 : ℝ) ≤ k := by linarith [(abs_le.mp hk).1]
  have hk0' : 0 ≤ k := by exact_mod_cast hk0
  have hcast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0'
  have h := binomial_central_mass_lower n k.toNat z r L hz hz1 hL hr hrn (by simpa only [hcast] using hk)
  simpa only [binomialIntegerMass, hk0', ↓reduceIte] using h

end MeanMaximumForests.PeakAnalysis
