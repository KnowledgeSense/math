import HilbertBipartite.CorrectionIdentity
import HilbertBipartite.BinomialTransform
import Mathlib.Data.Nat.Choose.Sum

open Finset Polynomial
namespace HilbertBipartite

noncomputable def correctionKernelBase (n : ℕ) : Polynomial ℚ :=
  ∑ r ∈ range (n / 2), X ^ r

@[simp] theorem correctionKernelBase_zero : correctionKernelBase 0 = 0 := by
  simp [correctionKernelBase]

@[simp] theorem correctionKernelBase_one : correctionKernelBase 1 = 0 := by
  simp [correctionKernelBase]

theorem correctionKernelBase_step (n : ℕ) :
    correctionKernelBase (n+2) = X * correctionKernelBase n + 1 := by
  unfold correctionKernelBase
  rw [Nat.add_div_right _ (by omega), sum_range_succ', mul_sum]
  simp only [pow_zero]
  congr 1
  apply sum_congr rfl
  intro r _
  rw [pow_succ']

noncomputable def correctionKernel (a n : ℕ) : Polynomial ℚ :=
  ∑ t ∈ range (n+1), C (a.multichoose t : ℚ) * X^t * correctionKernelBase (n-t)

@[simp] theorem correctionKernel_zero (a : ℕ) : correctionKernel a 0 = 0 := by
  simp [correctionKernel]

@[simp] theorem correctionKernel_one (a : ℕ) : correctionKernel a 1 = 0 := by
  norm_num [correctionKernel, sum_range_succ]

@[simp] theorem correctionKernel_zero_left (n : ℕ) :
    correctionKernel 0 n = correctionKernelBase n := by
  unfold correctionKernel
  rw [sum_range_succ']
  simp only [Nat.multichoose_zero_succ, Nat.cast_zero, map_zero, zero_mul, sum_const_zero,
    Nat.multichoose_zero_right, Nat.cast_one, map_one, pow_zero, one_mul, Nat.sub_zero, zero_add]

theorem correctionKernel_pascal (a n : ℕ) :
    correctionKernel (a+1) (n+1) = correctionKernel a (n+1) + X * correctionKernel (a+1) n := by
  unfold correctionKernel
  rw [sum_range_succ', sum_range_succ' (fun t =>
    C (a.multichoose t : ℚ) * X^t * correctionKernelBase (n+1-t))]
  simp only [Nat.multichoose_zero_right, Nat.cast_one, map_one, pow_zero, one_mul,
    Nat.sub_zero]
  simp_rw [Nat.multichoose_succ_succ, Nat.cast_add, map_add, add_mul]
  rw [sum_add_distrib, mul_sum]
  have h : (∑ t ∈ range (n+1),
      C ((a+1).multichoose t : ℚ) * X^(t+1) * correctionKernelBase (n+1-(t+1))) =
      ∑ t ∈ range (n+1), X * (C ((a+1).multichoose t : ℚ) * X^t * correctionKernelBase (n-t)) := by
    apply sum_congr rfl
    intro t _
    simp only [Nat.add_sub_add_right, pow_succ]
    ring
  rw [h]
  ring

theorem correctionKernelBase_eq_sum (n b : ℕ) (hn : n ≤ b) :
    correctionKernelBase n = ∑ r ∈ Icc 1 b,
      if 2*r ≤ n then (X : Polynomial ℚ)^(r-1) else 0 := by
  unfold correctionKernelBase
  rw [← sum_filter]
  apply sum_bij (fun r _ => r+1)
  · intro r hr
    have hr' := mem_range.mp hr
    simp only [mem_filter, mem_Icc]
    omega
  · intro r hr s hs he
    omega
  · intro r hr
    simp only [mem_filter, mem_Icc] at hr
    refine ⟨r-1, ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro r hr
    simp

theorem correctionKernel_eq_sum_bound (a n b : ℕ) (hn : n ≤ b) :
    correctionKernel a n = ∑ t ∈ range (b+1), ∑ r ∈ Icc 1 b,
      if t+2*r ≤ n then C (a.multichoose t : ℚ) * X^(t+r-1) else 0 := by
  unfold correctionKernel
  have he : (∑ t ∈ range (n+1),
      C (a.multichoose t : ℚ) * X^t * correctionKernelBase (n-t)) =
      ∑ t ∈ range (b+1),
        C (a.multichoose t : ℚ) * X^t * correctionKernelBase (n-t) := by
    apply sum_subset
    · intro t ht
      simp only [mem_range] at ht ⊢
      omega
    · intro t ht htn
      have htn' : n < t := by
        simp only [mem_range] at htn
        omega
      rw [Nat.sub_eq_zero_of_le (by omega), correctionKernelBase_zero, mul_zero]
  rw [he]
  apply sum_congr rfl
  intro t ht
  rw [correctionKernelBase_eq_sum (n-t) b (by omega), mul_sum]
  apply sum_congr rfl
  intro r hr
  have hr' := mem_Icc.mp hr
  have hc : 2*r ≤ n-t ↔ t+2*r ≤ n := by omega
  simp only [hc]
  split_ifs with h
  · rw [mul_assoc, ← pow_add, show t+(r-1)=t+r-1 by omega]
  · rw [mul_zero]

end HilbertBipartite
