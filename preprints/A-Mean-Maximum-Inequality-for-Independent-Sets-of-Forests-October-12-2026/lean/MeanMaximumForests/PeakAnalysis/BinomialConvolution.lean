import MeanMaximumForests.PeakAnalysis.BinomialInteger

namespace MeanMaximumForests.PeakAnalysis
open Finset

theorem binomial_convolution_integer (m n : ℕ) (k : ℤ) (z : ℝ) :
    binomialIntegerMass (m + n) z k =
      ∑ i ∈ range (m + 1), binomialSizeMass m z i * binomialIntegerMass n z (k - i) := by
  by_cases hk : 0 ≤ k
  · obtain ⟨K, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [binomialIntegerMass_natCast, binomial_convolution_nat]
    let f : ℕ → ℝ := fun i => binomialSizeMass m z i * binomialIntegerMass n z ((K : ℤ) - i)
    have hA : (∑ i ∈ range (K + 1), binomialSizeMass m z i * binomialSizeMass n z (K - i)) =
        ∑ i ∈ range (K + 1), f i := by
      apply sum_congr rfl
      intro i hi
      have hiK : i ≤ K := by have := mem_range.mp hi; omega
      simp only [f, ← Int.natCast_sub hiK, binomialIntegerMass_natCast]
    rw [hA]
    have hbigA : (∑ i ∈ range (K + 1), f i) = ∑ i ∈ range (m + K + 1), f i := by
      apply sum_subset (range_mono (by omega))
      intro i _ hi
      have hKi : K < i := by have := mem_range.not.mp hi; omega
      simp only [f, binomialIntegerMass_negative n z (by omega : (K : ℤ) - i < 0), mul_zero]
    have hbigB : (∑ i ∈ range (m + 1), f i) = ∑ i ∈ range (m + K + 1), f i := by
      apply sum_subset (range_mono (by omega))
      intro i _ hi
      have hmi : m < i := by have := mem_range.not.mp hi; omega
      simp only [f, binomialSizeMass_eq_zero z hmi, zero_mul]
    exact hbigA.trans hbigB.symm
  · rw [binomialIntegerMass_negative (m + n) z (by omega)]
    symm
    apply sum_eq_zero
    intro i _
    rw [binomialIntegerMass_negative n z (by omega : k - i < 0), mul_zero]

theorem binomial_integer_variation_bound (n j : ℕ) (z : ℝ) (hz : 0 < z) (hjn : j ≤ n)
    (hmode : ∀ k, binomialSizeMass n z k ≤ binomialSizeMass n z j) (S : Finset ℤ) :
    (∑ i ∈ S, |binomialIntegerMass n z (i + 1) - binomialIntegerMass n z i|) ≤
      2 * binomialSizeMass n z j := by
  let f : ℤ → ℝ := fun i => |binomialIntegerMass n z (i + 1) - binomialIntegerMass n z i|
  let T := (range (n + 2)).image (fun i : ℕ => (i : ℤ) - 1)
  have hzero : ∀ i, i ∉ T → f i = 0 := by
    intro i hi
    have hout : i < -1 ∨ (n : ℤ) < i := by
      by_contra! h
      apply hi
      apply mem_image.mpr
      refine ⟨(i + 1).toNat, ?_, ?_⟩
      · apply mem_range.mpr
        omega
      · omega
    rcases hout with hlo | hhi
    · simp only [f, binomialIntegerMass_negative n z (by omega : i + 1 < 0),
        binomialIntegerMass_negative n z (by omega : i < 0), sub_self, abs_zero]
    · simp only [f, binomialIntegerMass_above n z (by omega : (n : ℤ) < i + 1),
        binomialIntegerMass_above n z hhi, sub_self, abs_zero]
  have hle : (∑ i ∈ S, f i) ≤ ∑ i ∈ T, f i := by
    calc
      _ = ∑ i ∈ S ∩ T, f i := by
        symm
        apply sum_subset inter_subset_left
        intro i hiS hiI
        exact hzero i (by simp_all)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg inter_subset_right (by intros; exact abs_nonneg _)
  have htotal : (∑ i ∈ T, f i) = 2 * binomialSizeMass n z j := by
    rw [show T = (range (n + 2)).image (fun i : ℕ => (i : ℤ) - 1) from rfl]
    have hinj : Set.InjOn (fun i : ℕ => (i : ℤ) - 1) (range (n + 2)) := by
      intro a _ b _ h
      change (a : ℤ) - 1 = (b : ℤ) - 1 at h
      omega
    rw [sum_image hinj]
    rw [show n + 2 = (n + 1) + 1 by omega, sum_range_succ']
    have h0 : f (-1) = binomialSizeMass n z 0 := by
      change |binomialIntegerMass n z (-1 + 1) - binomialIntegerMass n z (-1)| = _
      rw [show (-1 : ℤ) + 1 = 0 by norm_num,
        binomialIntegerMass_negative n z (by norm_num : (-1 : ℤ) < 0), sub_zero]
      change |binomialSizeMass n z 0| = _
      exact abs_of_nonneg (by unfold binomialSizeMass; positivity)
    have hs : (∑ i ∈ range (n + 1), f (((i + 1 : ℕ) : ℤ) - 1)) =
        ∑ i ∈ range (n + 1), |binomialSizeMass n z (i + 1) - binomialSizeMass n z i| := by
      apply sum_congr rfl
      intro i _
      have hcast : ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) := by omega
      rw [hcast]
      change |binomialIntegerMass n z ((i : ℤ) + 1) - binomialIntegerMass n z i| = _
      rw [show (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) by omega]
      simp only [binomialIntegerMass_natCast]
    change (∑ i ∈ range (n + 1), f (((i + 1 : ℕ) : ℤ) - 1)) + f (-1) = _
    rw [hs, h0, add_comm]
    exact binomial_total_variation n j z hz hjn hmode
  exact hle.trans_eq htotal

end MeanMaximumForests.PeakAnalysis
