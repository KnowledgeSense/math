import HilbertBipartite.CorrectionRecurrence

open Finset Polynomial
namespace HilbertBipartite

theorem binomialTransform_correctionKernel_eq_sum (a b : ℕ) :
    binomialTransform (correctionKernel a) b =
      ∑ t ∈ range (b+1), ∑ r ∈ Icc 1 b, ∑ k ∈ Icc (t+2*r) b,
        C ((a.multichoose t : ℚ) * (b.choose k : ℚ)) * X^(t+r-1) := by
  calc
    _ = ∑ k ∈ range (b+1), ∑ t ∈ range (b+1), ∑ r ∈ Icc 1 b,
        if t+2*r ≤ k then
          C ((a.multichoose t : ℚ) * (b.choose k : ℚ)) * X^(t+r-1) else 0 := by
      unfold binomialTransform
      apply sum_congr rfl
      intro k hk
      have hkb : k ≤ b := by simpa only [mem_range, Nat.lt_succ_iff] using hk
      rw [correctionKernel_eq_sum_bound a k b hkb, mul_sum]
      apply sum_congr rfl
      intro t ht
      rw [mul_sum]
      apply sum_congr rfl
      intro r hr
      split_ifs
      · rw [map_mul]
        ring
      · rw [mul_zero]
    _ = ∑ t ∈ range (b+1), ∑ r ∈ Icc 1 b, ∑ k ∈ range (b+1),
        if t+2*r ≤ k then
          C ((a.multichoose t : ℚ) * (b.choose k : ℚ)) * X^(t+r-1) else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro t ht
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro t ht
      apply sum_congr rfl
      intro r hr
      rw [← sum_filter]
      apply sum_congr
      · ext k
        simp only [mem_filter, mem_range, mem_Icc]
        omega
      · intro k hk
        rfl

theorem correctionPolynomial_eq_binomialTransform (a b : ℕ) (ha : 1 ≤ a) :
    correctionPolynomial b a = binomialTransform (correctionKernel a) b := by
  rw [binomialTransform_correctionKernel_eq_sum]
  unfold correctionPolynomial
  apply sum_congr rfl
  intro t ht
  apply sum_congr rfl
  intro r hr
  apply sum_congr rfl
  intro k hk
  have hm : (t+a-1).choose (a-1) = a.multichoose t := by
    rw [Nat.multichoose_eq, Nat.add_comm a t]
    have ht' : t ≤ t+a-1 := by omega
    have he : t+a-1-t = a-1 := by omega
    simpa only [he] using Nat.choose_symm ht'
  rw [hm]

end HilbertBipartite
