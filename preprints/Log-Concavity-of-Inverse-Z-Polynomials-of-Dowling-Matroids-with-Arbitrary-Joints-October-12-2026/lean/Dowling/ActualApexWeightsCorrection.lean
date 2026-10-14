import Dowling.ActualApexWeightsRows
import Dowling.ActualApexWeightsPolynomial

noncomputable section
namespace Dowling
open Finset Polynomial
variable {G : Type*} [Group G] [Fintype G] [Subsingleton G]

theorem apex_fullP_top (h : ℕ) (hh : 1≤h) :
    ((fullP G (2*h-1)).coeff (h-1) : ℝ)=
      ((2*h).factorial : ℝ)*apexTauWeight h := by
  have hc : Fintype.card G=1 := Fintype.card_eq_one_iff.mpr ⟨1,fun x => Subsingleton.elim x 1⟩
  have he : ((fullP G (2*h-1)).coeff (h-1) : ℝ)=((fullP Unit (2*h-1)).coeff (h-1) : ℝ) := by
    by_cases h1 : h=1
    · subst h; simp [fullP_one]
    · rw [fullP_odd_top_source G h (by omega),fullP_odd_top_source Unit h (by omega),hc]
      simp
  rw [he,apexTauWeight]
  have hf : ((2*h).factorial : ℝ)≠0 := by positivity
  field_simp

theorem apex_fullY_coeff (n k : ℕ) :
    ((fullY G n).coeff k : ℝ)=(n.factorial : ℝ)*
      quadraticWeightedRow (dowlingBaseWeight 1 n) 2 n k := by
  have hc : Fintype.card G=1 := Fintype.card_eq_one_iff.mpr ⟨1,fun x => Subsingleton.elim x 1⟩
  simpa [hc,show (1 : ℝ)+1=2 by norm_num] using fullY_coeff_base_weight G n k

theorem apex_rankCorrection_coeff (n h k : ℕ) (hh : 1≤h) (hn : 2*h≤n) :
    ((jointRankCorrection G n (2*h)).coeff k : ℝ)=
      ((2*h).factorial : ℝ)*apexTauWeight h*((n-2*h).factorial : ℝ)*
      quadraticWeightedRow (shiftedQuadraticWeight h (dowlingBaseWeight 1 (n-2*h))) 2 n k := by
  rw [jointRankCorrection,ite_eq_left (by omega),show (2*h-1)/2=h-1 by omega,
    show 2*h/2=h by omega,mul_assoc,coeff_C_mul,coeff_X_pow_mul',Int.cast_mul,
    apex_fullP_top h hh,quadraticWeightedRow_shift h _ 2 n k hn]
  by_cases hk : h≤k
  · rw [ite_eq_left hk,apex_fullY_coeff]
    by_cases hkn : k+h≤n
    · rw [ite_eq_left ⟨hk,hkn⟩]; ring
    · rw [ite_eq_right (by omega),quadraticWeightedRow,ite_eq_right (by omega)]
      ring
  · rw [ite_eq_right hk,Int.cast_zero,ite_eq_right (by omega)]
    ring

omit [Subsingleton G] in
theorem missingJointCorrection_even (n ell : ℕ) :
    missingJointCorrection G n ell=
      ∑ h∈Icc 1 (n/2),C (ell.choose (2*h) : ℤ)*jointRankCorrection G n (2*h) := by
  rw [missingJointCorrection,dowling_sum_even]
  · symm
    apply Finset.sum_subset
    · intro h hh
      have hh' := mem_Icc.mp hh
      exact mem_range.mpr (by omega)
    · intro h hh hnot
      have hh' := mem_range.mp hh
      have hz : h=0 := by simp only [mem_Icc,not_and_or,not_le] at hnot; omega
      subst h
      simp [jointRankCorrection]
  · intro j
    simp [jointRankCorrection]

end Dowling
