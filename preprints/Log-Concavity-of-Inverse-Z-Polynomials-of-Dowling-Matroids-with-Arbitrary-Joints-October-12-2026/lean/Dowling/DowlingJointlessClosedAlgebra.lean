import Dowling.DowlingJointlessBase
import Mathlib.Data.Nat.Factorial.Cast

noncomputable section
namespace Dowling

def jointlessShiftedQuadratic (c : ℝ) (j h : ℕ) : ℝ :=
  if h≤j then dowlingQuadraticWeight c (j-h) else 0

theorem jointlessShiftedQuadratic_factor {c : ℝ} (hc : c≠0) (j h : ℕ) :
    jointlessShiftedQuadratic c j h=
      c^j/(j.factorial:ℝ)*(j.descFactorial h:ℝ)*(c-j+h)/c^(h+1) := by
  by_cases hh : h≤j
  · rw [jointlessShiftedQuadratic,ite_eq_left hh,dowlingQuadraticWeight_factor hc,
      Nat.cast_sub hh]
    have hf : ((j-h).factorial:ℝ)*(j.descFactorial h:ℝ)=(j.factorial:ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hh
    have hp : c^(j-h)*c^h=c^j := by rw [← pow_add,Nat.sub_add_cancel hh]
    have hfac : ((j-h).factorial:ℝ)≠0 := by positivity
    have hfacj : (j.factorial:ℝ)≠0 := by positivity
    field_simp
    rw [← hf,← hp,pow_succ]
    ring
  · rw [jointlessShiftedQuadratic,ite_eq_right hh,
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

theorem jointlessShiftedQuadratic_one (c : ℝ) (j : ℕ) :
    jointlessShiftedQuadratic c j 1=if j=0 then 0 else dowlingQuadraticWeight c (j-1) := by
  by_cases hj : j=0
  · subst j; simp [jointlessShiftedQuadratic]
  · simp [jointlessShiftedQuadratic,hj,show 1≤j by omega]

theorem jointlessShiftedQuadratic_two (c : ℝ) (j : ℕ) :
    jointlessShiftedQuadratic c j 2=if j<2 then 0 else dowlingQuadraticWeight c (j-2) := by
  by_cases hj : j<2 <;> simp [jointlessShiftedQuadratic,hj,show (2≤j)↔¬j<2 by omega]

def jointlessRemovedFactor (a μ j : ℝ) : ℝ :=
  (a*(2*μ+1-a)/(2*μ))*(μ-j)/μ+
    a*(1-a)*j*(μ-j+1)/μ^2+(a^2/3)*j*(j-1)*(μ-j+2)/μ^3

theorem jointlessUnraisedWeight_factor {a : ℝ} (n j : ℕ)
    (hm : (n+a-1)/2≠0) (hl : (n+a)/2≠0) :
    jointlessUnraisedWeight a n j=
      ((n+a)/2)^j/(j.factorial:ℝ)*(((n+a)/2-j)/((n+a)/2))-
      ((n+a-1)/2)^j/(j.factorial:ℝ)*jointlessRemovedFactor a ((n+a-1)/2) j := by
  have hone (c : ℝ) :
      (if j=0 then 0 else a*(1-a)*dowlingQuadraticWeight c (j-1))=
        a*(1-a)*jointlessShiftedQuadratic c j 1 := by
    rw [jointlessShiftedQuadratic_one]
    split <;> simp
  have htwo (c : ℝ) :
      (if j<2 then 0 else (a^2/3)*dowlingQuadraticWeight c (j-2))=
        (a^2/3)*jointlessShiftedQuadratic c j 2 := by
    rw [jointlessShiftedQuadratic_two]
    split <;> simp
  rw [jointlessUnraisedWeight,hone,htwo,
    jointlessShiftedQuadratic_factor hm,jointlessShiftedQuadratic_factor hm,
    dowlingQuadraticWeight_factor hl,dowlingQuadraticWeight_factor hm]
  simp only [Nat.descFactorial_one,Nat.cast_descFactorial_two,Nat.cast_one,Nat.cast_ofNat]
  unfold jointlessRemovedFactor
  have hn : (n:ℝ)+a-1≠0 := by intro h; apply hm; rw [h]; norm_num
  field_simp
  ring

end Dowling
