import Dowling.DowlingRetainedPayment

noncomputable section
namespace Dowling
open Finset

/-- Decreasing nonnegative multipliers preserve a nonpositive sum with one sign crossing. -/
theorem apex_single_crossing_attenuation (x t : ℕ→ℝ) (N : ℕ)
    (ht : ∀i,i<N→0≤t i) (hanti : ∀i j,i≤j→j<N→t j≤t i)
    (hcross : ∀i j,i<j→j<N→0<x i→0≤x j)
    (hsum : (∑i∈range N,x i)≤0) : (∑i∈range N,t i*x i)≤0 := by
  by_cases hex : ∃i,i<N ∧ 0<x i
  · let c := Nat.find hex
    have hc : c<N ∧ 0<x c := Nat.find_spec hex
    have hterm (i : ℕ) (hi : i∈range N) : t i*x i≤t c*x i := by
      have hiN := mem_range.mp hi
      by_cases hci : c ≤ i
      · have hxi : 0≤x i := by
          rcases eq_or_lt_of_le hci with rfl | hlt
          · exact hc.2.le
          · exact hcross c i hlt hiN hc.2
        exact mul_le_mul_of_nonneg_right (hanti c i hci hiN) hxi
      · have hic : i < c := by omega
        have hxi : x i≤0 := by
          have hnot := Nat.find_min hex hic
          exact le_of_not_gt (fun h=>hnot ⟨hiN,h⟩)
        exact mul_le_mul_of_nonpos_right (hanti i c (by omega) hc.1) hxi
    calc
      _ ≤ ∑i∈range N,t c*x i := sum_le_sum hterm
      _ = t c*∑i∈range N,x i := by rw [mul_sum]
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (ht c hc.1) hsum
  · apply sum_nonpos
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (ht i (mem_range.mp hi))
      (le_of_not_gt (fun h=>hex ⟨i,mem_range.mp hi,h⟩))

/-- A common curvature budget transfers through the same one-crossing attenuation. -/
theorem apex_curvature_attenuation (f d t : ℕ→ℝ) (N : ℕ) (L : ℝ)
    (ht : ∀i,i<N→0≤t i) (hanti : ∀i j,i≤j→j<N→t j≤t i)
    (hcross : ∀i j,i<j→j<N→0<d i-L*f i→0≤d j-L*f j)
    (hbudget : (∑i∈range N,d i)≤L*(∑i∈range N,f i)) :
    (∑i∈range N,t i*d i)≤L*(∑i∈range N,t i*f i) := by
  have hsum : (∑i∈range N,(d i-L*f i))≤0 := by
    rw [sum_sub_distrib,← mul_sum]
    linarith
  have h := apex_single_crossing_attenuation (fun i=>d i-L*f i) t N ht hanti hcross hsum
  simp only [mul_sub,Finset.sum_sub_distrib] at h
  have heq : (∑i∈range N,t i*(L*f i))=L*(∑i∈range N,t i*f i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [heq] at h
  linarith

end Dowling
