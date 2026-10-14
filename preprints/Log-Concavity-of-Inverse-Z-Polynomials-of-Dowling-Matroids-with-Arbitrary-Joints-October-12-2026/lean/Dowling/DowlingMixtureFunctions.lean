import Dowling.DowlingMixturePointwise

noncomputable section
namespace Dowling
open Finset

theorem dowlingMixtureFunction_nonneg {c p : ℝ} (n k : ℕ)
    (hc : (n : ℝ)/2<c) (hp : 1<p) (j : ℤ) : 0≤dowlingMixtureFunction c p n k j := by
  by_cases hj : j<0
  · simp [dowlingMixtureFunction,hj]
  · rw [dowlingMixtureFunction,ite_eq_right hj]
    exact dowlingMixtureTerm_nonneg n k j.toNat hc hp

theorem dowlingMixtureFunction_support (c p : ℝ) (n k : ℕ) (j : ℤ)
    (hj : j < 0 ∨ (n : ℤ) < j) : dowlingMixtureFunction c p n k j=0 := by
  rcases hj with hj | hj
  · simp [dowlingMixtureFunction,hj]
  · rw [dowlingMixtureFunction,ite_eq_right (by omega),dowlingMixtureTerm,
      ite_eq_right (by omega)]

theorem dowlingMixtureFunction_sum (c p : ℝ) (n k : ℕ) :
    (∑ j ∈ range (n+1),dowlingMixtureFunction c p n k j)=dowlingWeightedCoefficient c p n k := by
  simp only [dowlingMixtureFunction,Int.natCast_nonneg,not_lt,ite_eq_right,
    Int.toNat_natCast]
  by_cases hk : k≤n
  · rw [dowlingWeightedCoefficient,ite_eq_left hk]
    symm
    calc
      _ = ∑ j ∈ range (min k (n-k)+1),dowlingMixtureTerm c p n k j := by
        apply sum_congr rfl
        intro j hj
        rw [dowlingMixtureTerm,ite_eq_left (by have := mem_range.mp hj; omega)]
      _ = _ := by
        apply sum_subset
        · intro j hj
          apply mem_range.mpr
          have := mem_range.mp hj
          omega
        · intro j hj hnot
          rw [dowlingMixtureTerm,ite_eq_right (by simp only [mem_range] at hnot; omega)]
  · rw [dowlingWeightedCoefficient,ite_eq_right hk]
    apply sum_eq_zero
    intro j hj
    rw [dowlingMixtureTerm,ite_eq_right (by omega)]

theorem dowlingMixtureFunction_sum_pos {c p : ℝ} (n k : ℕ) (hc : (n : ℝ)/2<c)
    (hp : 1<p) (hk : k≤n) :
    0<∑ j ∈ range (n+1),dowlingMixtureFunction c p n k j := by
  apply sum_pos'
  · intro j hj
    exact dowlingMixtureFunction_nonneg n k hc hp j
  · refine ⟨0,mem_range.mpr (by omega),?_⟩
    simp only [Nat.cast_zero,dowlingMixtureFunction,lt_self_iff_false,ite_false,Int.toNat_zero]
    exact dowlingMixtureTerm_pos n k 0 hc hp (by omega)

theorem dowlingMixtureFunction_midpoint_strict {c p : ℝ} (n k : ℕ)
    (hc : (n : ℝ)/2<c) (hp : 1<p) (hk : 1≤k) (hkn : k<n) (i j : ℤ)
    (hpos : 0<dowlingMixtureFunction c p n (k-1) i*dowlingMixtureFunction c p n (k+1) j) :
    dowlingMixtureFunction c p n (k-1) i*dowlingMixtureFunction c p n (k+1) j <
      dowlingMixtureFunction c p n k ((i+j)/2)*dowlingMixtureFunction c p n k ((i+j+1)/2) := by
  have hi : ¬i<0 := by
    intro hi
    simp [dowlingMixtureFunction,hi] at hpos
  have hj : ¬j<0 := by
    intro hj
    simp [dowlingMixtureFunction,hj] at hpos
  have hi' : i.toNat≤k-1 ∧ k-1+i.toNat≤n := by
    by_contra hh
    have hz : dowlingMixtureFunction c p n (k-1) i=0 := by
      rw [dowlingMixtureFunction,ite_eq_right hi,dowlingMixtureTerm,ite_eq_right hh]
    rw [hz,zero_mul] at hpos
    exact lt_irrefl _ hpos
  have hj' : j.toNat≤k+1 ∧ k+1+j.toNat≤n := by
    by_contra hh
    have hz : dowlingMixtureFunction c p n (k+1) j=0 := by
      rw [dowlingMixtureFunction,ite_eq_right hj,dowlingMixtureTerm,ite_eq_right hh]
    rw [hz,mul_zero] at hpos
    exact lt_irrefl _ hpos
  have h := dowlingMixtureTerm_midpoint_strict n k i.toNat j.toNat hc hp hk hkn hi' hj'
  have hu : ¬(i+j)/2<0 := by omega
  have hv : ¬(i+j+1)/2<0 := by omega
  have hue : ((i+j)/2).toNat=(i.toNat+j.toNat)/2 := by omega
  have hve : ((i+j+1)/2).toNat=(i.toNat+j.toNat+1)/2 := by omega
  simpa only [dowlingMixtureFunction,ite_eq_right hi,ite_eq_right hj,
    ite_eq_right hu,ite_eq_right hv,hue,hve] using h

end Dowling
