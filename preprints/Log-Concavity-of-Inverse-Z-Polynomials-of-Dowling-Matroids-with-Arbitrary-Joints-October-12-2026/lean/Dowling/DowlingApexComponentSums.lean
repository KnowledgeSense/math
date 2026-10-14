import Dowling.DowlingApexComponents

noncomputable section
namespace Dowling
open Finset

theorem apexChooseRatio_predecessor (B z : ℕ) (hB : 0<B) (hz : z≤B) :
    apexChooseRatio (B-1) B z=((B-z:ℕ):ℝ)/B := by
  have h := Nat.choose_mul_succ_eq (B-1) z
  rw [show B-1+1=B by omega] at h
  have hR : ((B-1).choose z:ℝ)*B=(B.choose z:ℝ)*(B-z:ℕ) := by exact_mod_cast h
  have hb : (B:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hB
  have hc : (B.choose z:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hz)
  unfold apexChooseRatio
  field_simp
  nlinarith

theorem apexAttenuation_one_joint (n h : ℕ) (hn : 2≤n) (hh : 2*h≤n) :
    apexAttenuation n 1 h=1 := by
  by_cases h0 : h=0
  · simp [apexAttenuation,h0]
  · rw [apexAttenuation,ite_eq_right h0,apexChooseRatio_predecessor (n-1) (2*h-1)
      (by omega) (by omega)]
    have hn0 : ((n-1:ℕ):ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0<n-1)
    have hh0 : ((2*h-1:ℕ):ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0<2*h-1)
    rw [Nat.cast_sub (by omega : 2*h-1≤n-1)]
    simp only [Nat.cast_one,div_one]
    field_simp
    ring

theorem apexNormalizedWeight_components (n k j : ℕ) (hk : 1≤k) (hkn : k≤n)
    (hj : 2*j≤n) :
    apexNormalizedWeight n k j=(k:ℝ)*∑h∈range (j+1),apexAttenuation n k h*apexComponent n h j := by
  have hset : range (j+1)=insert 0 (Icc 1 j) := by ext h; simp; omega
  rw [hset,sum_insert (by simp),mul_add,mul_sum]
  simp only [apexAttenuation,ite_true,apexComponent,apexComponentCoefficient,
    apexF_zero_component,mul_one,one_mul]
  unfold apexNormalizedWeight
  congr 1
  · ring
  · apply sum_congr rfl
    intro h hh
    have hpos : 1≤h := (mem_Icc.mp hh).1
    have hhj : h≤j := (mem_Icc.mp hh).2
    have heq := apexAttenuation_coefficient n k h hk hkn hpos (by omega)
    simp only [apexAttenuation,ite_eq_right (by omega : h≠0)] at heq
    simp only [ite_eq_right (by omega : h≠0)]
    rw [← heq]
    ring

theorem apexNormalizedWeight_components_extended (n k j N : ℕ) (hk : 1≤k) (hkn : k≤n)
    (hj : 2*j≤n) (hjN : j<N) :
    apexNormalizedWeight n k j=(k:ℝ)*∑h∈range N,apexAttenuation n k h*apexComponent n h j := by
  rw [apexNormalizedWeight_components n k j hk hkn hj]
  congr 1
  apply sum_subset
  · intro h hh
    simp only [mem_range] at *
    omega
  · intro h hh hnot
    have hhj : ¬h≤j := by simp only [mem_range] at hnot; omega
    simp [apexComponent,apexF,hhj]

theorem apexNormalizedWeight_one_components (n j N : ℕ) (hn : 2≤n)
    (hjN : j<N) (hN : 2*(N-1)≤n) :
    apexNormalizedWeight n 1 j=∑h∈range N,apexComponent n h j := by
  rw [apexNormalizedWeight_components_extended n 1 j N le_rfl (by omega) (by omega) hjN]
  simp only [Nat.cast_one,one_mul]
  apply sum_congr rfl
  intro h hh
  rw [apexAttenuation_one_joint n h hn (by have := mem_range.mp hh; omega),one_mul]

end Dowling
