import MeanMaximumForests.PeakAnalysis.BinomialConvolution

namespace MeanMaximumForests.PeakAnalysis
open Finset

theorem binomial_integer_gradient_mode (m n a b : ℕ) (k : ℤ) (z : ℝ) (hz : 0 < z)
    (hb : b ≤ n)
    (hA : ∀ i, binomialSizeMass m z i ≤ binomialSizeMass m z a)
    (hB : ∀ i, binomialSizeMass n z i ≤ binomialSizeMass n z b) :
    |binomialIntegerMass (m + n) z (k + 1) - binomialIntegerMass (m + n) z k| ≤
      2 * binomialSizeMass m z a * binomialSizeMass n z b := by
  let A := binomialSizeMass m z a
  let f : ℤ → ℝ := fun i => |binomialIntegerMass n z (i + 1) - binomialIntegerMass n z i|
  have hA0 : 0 ≤ A := by dsimp [A, binomialSizeMass]; positivity
  have hsum : (∑ i ∈ range (m + 1), f (k - i)) ≤ 2 * binomialSizeMass n z b := by
    have hinj : Set.InjOn (fun i : ℕ => k - (i : ℤ)) (range (m + 1)) := by
      intro a _ b _ hab
      change k - (a : ℤ) = k - (b : ℤ) at hab
      omega
    rw [← sum_image hinj]
    exact binomial_integer_variation_bound n b z hz hb hB _
  calc
    _ = |∑ i ∈ range (m + 1), binomialSizeMass m z i *
        (binomialIntegerMass n z ((k - i) + 1) - binomialIntegerMass n z (k - i))| := by
      rw [binomial_convolution_integer, binomial_convolution_integer, ← sum_sub_distrib]
      congr 1
      apply sum_congr rfl
      intro i _
      rw [show k + 1 - (i : ℤ) = (k - i) + 1 by omega]
      ring
    _ ≤ ∑ i ∈ range (m + 1), |binomialSizeMass m z i *
        (binomialIntegerMass n z ((k - i) + 1) - binomialIntegerMass n z (k - i))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (m + 1), A * f (k - i) := by
      apply sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (show 0 ≤ binomialSizeMass m z i by unfold binomialSizeMass; positivity)]
      exact mul_le_mul_of_nonneg_right (hA i) (abs_nonneg _)
    _ = A * ∑ i ∈ range (m + 1), f (k - i) := (mul_sum _ _ _).symm
    _ ≤ A * (2 * binomialSizeMass n z b) := mul_le_mul_of_nonneg_left hsum hA0
    _ = _ := by dsimp [A]; ring

/-- Uniform order-inverse-size bound for the adjacent difference, including indices outside support. -/
theorem binomial_integer_gradient_large (n : ℕ) (k : ℤ) (z : ℝ)
    (hz : (1 / 4 : ℝ) ≤ z) (hz1 : z ≤ 1) (hn : 28802 ≤ n) :
    (n : ℝ) * |binomialIntegerMass n z (k + 1) - binomialIntegerMass n z k| ≤
      6 * (Real.exp 720) ^ 2 := by
  have hz0 : 0 < z := by linarith
  let m := n / 2
  let l := n - m
  have hm : 14401 ≤ m := by dsimp [m]; omega
  have hl : 14401 ≤ l := by dsimp [m, l]; omega
  have hsum : m + l = n := by dsimp [l, m]; omega
  have hbalance : m ≤ l ∧ l ≤ m + 1 := by dsimp [l, m]; omega
  let r := Real.sqrt (m : ℝ)
  let s := Real.sqrt (l : ℝ)
  have hr2 : r ^ 2 = m := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs2 : s ^ 2 = l := Real.sq_sqrt (Nat.cast_nonneg _)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hr : 120 ≤ r := by
    have h : (14401 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hs : 120 ≤ s := by
    have h : (14401 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith
  have hmn : (m : ℝ) + l = n := by exact_mod_cast hsum
  have hml : (m : ℝ) ≤ l := by exact_mod_cast hbalance.1
  have hlm : (l : ℝ) ≤ m + 1 := by exact_mod_cast hbalance.2
  have hprod : (n : ℝ) ≤ 3 * (r * s) := by
    have hsq : (r * s) ^ 2 = (m : ℝ) * l := by rw [mul_pow, hr2, hs2]
    have hh : 0 ≤ ((l : ℝ) - m) * (1 - ((l : ℝ) - m)) := mul_nonneg (by linarith) (by linarith)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hmm : (m : ℝ) ≤ (m : ℝ) * l := by nlinarith
    nlinarith [mul_nonneg hr0 hs0]
  obtain ⟨a, _, _, hA⟩ := exists_binomial_mode m z hz0
  obtain ⟨b, hbl, _, hB⟩ := exists_binomial_mode l z hz0
  have hgrad := binomial_integer_gradient_mode m l a b k z hz0 hbl hA hB
  rw [hsum] at hgrad
  have hupperA := binomial_mass_upper_large m a z r hz hz1 hr hr2
  have hupperB := binomial_mass_upper_large l b z s hz hz1 hs hs2
  have hA0 : 0 ≤ binomialSizeMass m z a := by unfold binomialSizeMass; positivity
  have hB0 : 0 ≤ binomialSizeMass l z b := by unfold binomialSizeMass; positivity
  have hmul := mul_le_mul hupperA hupperB (mul_nonneg hs0 hB0) (Real.exp_pos 720).le
  have hscaled := mul_le_mul_of_nonneg_left hgrad (mul_nonneg hr0 hs0)
  have hnscaled := mul_le_mul_of_nonneg_right hprod
    (abs_nonneg (binomialIntegerMass n z (k + 1) - binomialIntegerMass n z k))
  nlinarith only [hmul, hscaled, hnscaled]

end MeanMaximumForests.PeakAnalysis
