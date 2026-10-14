import Dowling.DowlingInverseZCandidateCoefficients

noncomputable section
namespace Dowling
open Finset

@[simp] theorem dowlingQuadraticWeight_zero (c : ℝ) : dowlingQuadraticWeight c 0=1 := by
  simp [dowlingQuadraticWeight]

theorem dowlingQuadraticWeight_succ (c : ℝ) (j : ℕ) :
    dowlingQuadraticWeight c (j+1)=(c-(j+1))*c^j/(j+1).factorial := by
  simp only [dowlingQuadraticWeight,Nat.add_one_ne_zero,ite_false,add_tsub_cancel_right]
  rw [Nat.factorial_succ,pow_succ]
  push_cast
  have hj : (j.factorial : ℝ)≠0 := by positivity
  have hj1 : (j+1 : ℝ)≠0 := by positivity
  field_simp

theorem dowlingQuadraticWeight_pos {c : ℝ} {j : ℕ} (hc : 0<c) (hj : (j : ℝ)<c) :
    0<dowlingQuadraticWeight c j := by
  cases j with
  | zero => simp
  | succ j =>
    rw [dowlingQuadraticWeight_succ]
    apply div_pos
    · apply mul_pos
      · exact sub_pos.mpr (by exact_mod_cast hj)
      · positivity
    · positivity

theorem dowlingScalarCoefficient_pos {a : ℝ} (ha : 0<a) (n k : ℕ) (hk : k≤n) :
    0<dowlingScalarCoefficient a n k := by
  rw [dowlingScalarCoefficient,ite_eq_left hk]
  apply Finset.sum_pos'
  · intro j hj
    have hjn : 2*j≤n := by have := mem_range.mp hj; omega
    have hc : 0<((n : ℝ)+a)/2 := by positivity
    have hjc : (j : ℝ)<((n : ℝ)+a)/2 := by
      have : (2 : ℝ)*j≤n := by exact_mod_cast hjn
      linarith
    exact le_of_lt (mul_pos (mul_pos (dowlingQuadraticWeight_pos hc hjc)
      (dowlingBinomialWeight_pos ha _)) (dowlingBinomialWeight_pos ha _))
  · refine ⟨0,mem_range.mpr (by omega),?_⟩
    simp only [dowlingQuadraticWeight_zero,one_mul,Nat.sub_zero]
    exact mul_pos (dowlingBinomialWeight_pos ha _) (dowlingBinomialWeight_pos ha _)

theorem dowlingScalarCoefficient_symm (a : ℝ) (n k : ℕ) (hk : k≤n) :
    dowlingScalarCoefficient a n (n-k)=dowlingScalarCoefficient a n k := by
  rw [dowlingScalarCoefficient,dowlingScalarCoefficient,ite_eq_left (by omega),ite_eq_left hk,
    Nat.sub_sub_self hk,min_comm]
  apply sum_congr rfl
  intro j hj
  ring

theorem dowlingScalarCoefficient_above (a : ℝ) (n k : ℕ) (hk : n<k) :
    dowlingScalarCoefficient a n k=0 := by
  rw [dowlingScalarCoefficient,ite_eq_right (by omega)]

end Dowling
