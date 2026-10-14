import Dowling.ActualApexWeightsSingleIdentification
import Dowling.DowlingApexPayment

noncomputable section
namespace Dowling

theorem apex_gaussian_shift (c : ℝ) (hc : c≠0) (j : ℕ) :
    (if j=0 then 0 else c^(j-1)/((j-1).factorial : ℝ))=
      (j : ℝ)/c*(c^j/(j.factorial : ℝ)) := by
  cases j with
  | zero => simp
  | succ j =>
    simp only [Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel_right,Nat.factorial_succ,
      Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    have hj : (j : ℝ)+1≠0 := by positivity
    have hf : (j.factorial : ℝ)≠0 := by positivity
    field_simp

theorem apex_corrected_gaussian (c : ℝ) (hc : c≠0) (j : ℕ) :
    dowlingQuadraticWeight c j=(1-(j : ℝ)/c)*(c^j/(j.factorial : ℝ)) := by
  rw [dowlingQuadraticWeight,apex_gaussian_shift c hc j]
  ring

theorem apex_corrected_gaussian_shift (c : ℝ) (hc : c≠0) (j : ℕ) :
    (if j=0 then 0 else dowlingQuadraticWeight c (j-1))=
      (j : ℝ)/c*(1-((j : ℝ)-1)/c)*(c^j/(j.factorial : ℝ)) := by
  cases j with
  | zero => simp
  | succ j =>
    simp only [Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel_right]
    rw [apex_corrected_gaussian c hc j]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    have hj : (j : ℝ)+1≠0 := by positivity
    have hf : (j.factorial : ℝ)≠0 := by positivity
    field_simp
    ring

theorem apexSingleUnraised_formula (n j : ℕ) (hn : 0<n) :
    apexSingleUnraised n j=(1-(j : ℝ)*((j : ℝ)-1)/((n : ℝ)/2)^2)*
      (((n : ℝ)/2)^j/(j.factorial : ℝ)) := by
  have hc : (n : ℝ)/2≠0 := by positivity
  rw [apexSingleUnraised,apex_corrected_gaussian _ hc,apex_corrected_gaussian_shift _ hc]
  field_simp
  ring

theorem apexSingleUnraised_shift_formula (n j : ℕ) (hn : 0<n) :
    (if j=0 then 0 else apexSingleUnraised n (j-1))=
      (j : ℝ)/((n : ℝ)/2)*(1-((j : ℝ)-1)*((j : ℝ)-2)/((n : ℝ)/2)^2)*
        (((n : ℝ)/2)^j/(j.factorial : ℝ)) := by
  cases j with
  | zero => simp
  | succ j =>
    simp only [Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel_right]
    rw [apexSingleUnraised_formula n j hn]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    have hj : (j : ℝ)+1≠0 := by positivity
    have hf : (j.factorial : ℝ)≠0 := by positivity
    have hc : (n : ℝ)/2≠0 := by positivity
    field_simp
    ring

end Dowling
