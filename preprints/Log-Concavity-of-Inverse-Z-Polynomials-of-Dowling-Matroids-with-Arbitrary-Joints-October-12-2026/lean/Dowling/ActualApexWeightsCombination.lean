import Dowling.ActualApexWeightsMissing

noncomputable section
namespace Dowling
open Finset

theorem apexRaisedWeight_combination (n k j : ℕ) (hj : 2*j≤n) :
    apexRaisedWeight n k j=(k : ℝ)/n*dowlingBaseWeight 1 n j+
      (((n-k : ℕ) : ℝ)/n)*apexMissingWeight n n j-apexMissingWeight n (n-k) j := by
  have hsum : ∀ ell,apexMissingWeight n ell j=
      ∑ h∈Icc 1 j,((ell.choose (2*h) : ℝ)/(n.choose (2*h) : ℝ))*apexTauWeight h*
        (dowlingBaseWeight 1 n j*apexF n h j) := by
    intro ell
    rw [apexMissingWeight]
    symm
    apply Finset.sum_subset_zero_on_sdiff
    · intro h hh
      have hh' := mem_Icc.mp hh
      apply mem_Icc.mpr
      omega
    · intro h hh
      have hh' := mem_sdiff.mp hh
      have hn := mem_Icc.mp hh'.1
      have hjh : ¬h≤j := by intro he; exact hh'.2 (mem_Icc.mpr ⟨hn.1,he⟩)
      simp [shiftedQuadraticWeight,hjh]
    · intro h hh
      have hh' := mem_Icc.mp hh
      rw [shiftedQuadraticWeight,ite_eq_left hh'.2,apexF_base_ratio n h j hh'.2 hj]
  rw [apexRaisedWeight,apexNormalizedWeight,hsum n,hsum (n-k),mul_add,
    Finset.mul_sum,Finset.mul_sum,add_sub_assoc,← Finset.sum_sub_distrib]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro h hh
    have hh' := mem_Icc.mp hh
    have hc : (n.choose (2*h) : ℝ)≠0 := by exact_mod_cast (Nat.choose_pos (by omega : 2*h≤n)).ne'
    rw [div_self hc]
    ring

end Dowling
