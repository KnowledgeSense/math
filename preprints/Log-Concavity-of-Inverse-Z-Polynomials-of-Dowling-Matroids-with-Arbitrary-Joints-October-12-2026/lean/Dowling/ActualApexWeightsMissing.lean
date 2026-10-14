import Dowling.ActualApexWeightsCorrection

noncomputable section
namespace Dowling
open Finset Polynomial

def apexMissingWeight (n ell j : ℕ) : ℝ :=
  ∑ h∈Icc 1 (n/2), ((ell.choose (2*h) : ℝ)/(n.choose (2*h) : ℝ))*
    apexTauWeight h*shiftedQuadraticWeight h (dowlingBaseWeight 1 (n-2*h)) j

theorem apex_choose_factorial (n h : ℕ) (hn : 2*h≤n) :
    ((2*h).factorial : ℝ)*((n-2*h).factorial : ℝ)=
      (n.factorial : ℝ)/(n.choose (2*h) : ℝ) := by
  have hc : (n.choose (2*h) : ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hn).ne'
  apply (eq_div_iff hc).mpr
  have hf : (n.choose (2*h) : ℝ)*((2*h).factorial : ℝ)*((n-2*h).factorial : ℝ)=n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hn
  nlinarith only [hf]

variable {G : Type*} [Group G] [Fintype G] [Subsingleton G]

theorem apex_missing_coeff (n ell k : ℕ) :
    ((missingJointCorrection G n ell).coeff k : ℝ)=
      (n.factorial : ℝ)*quadraticWeightedRow (apexMissingWeight n ell) 2 n k := by
  rw [missingJointCorrection_even]
  simp only [finsetSum_coeff,coeff_C_mul,Int.cast_sum,Int.cast_mul,Int.cast_natCast]
  change _=(n.factorial : ℝ)*quadraticWeightedRow (fun j =>
    ∑ h∈Icc 1 (n/2), ((ell.choose (2*h) : ℝ)/(n.choose (2*h) : ℝ))*
      apexTauWeight h*shiftedQuadraticWeight h (dowlingBaseWeight 1 (n-2*h)) j) 2 n k
  rw [quadraticWeightedRow_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hh' := Finset.mem_Icc.mp hh
  have hn : 2*h≤n := by omega
  rw [apex_rankCorrection_coeff n h k hh'.1 hn,quadraticWeightedRow_scalar]
  have hf := apex_choose_factorial n h hn
  calc
    _ = (ell.choose (2*h) : ℝ)*(((2*h).factorial : ℝ)*((n-2*h).factorial : ℝ))*apexTauWeight h*
      quadraticWeightedRow (shiftedQuadraticWeight h (dowlingBaseWeight 1 (n-2*h))) 2 n k := by ring
    _ = _ := by rw [hf]; ring

end Dowling
