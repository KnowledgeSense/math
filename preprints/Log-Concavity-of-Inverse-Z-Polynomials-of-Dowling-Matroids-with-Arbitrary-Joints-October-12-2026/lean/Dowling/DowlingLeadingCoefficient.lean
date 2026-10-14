import Dowling.DowlingLeadingQuadratic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

noncomputable section
namespace Dowling
open PowerSeries

 theorem derivative_dowlingLeadingLog (m : ℝ) :
    derivative (dowlingLeadingLog m)=C (Polynomial.C m⁻¹)*(1-C Polynomial.X*X^2) := by
  have hc : (3 : PowerSeries (Polynomial ℝ))*C (Polynomial.C (1/3 : ℝ))=1 := by
    have h := congrArg (fun r : ℝ => (C (Polynomial.C r) : PowerSeries (Polynomial ℝ)))
      (show (3 : ℝ)*(1/3)=1 by norm_num)
    simpa only [map_mul,map_ofNat,map_one] using h
  simp only [dowlingLeadingLog,Derivation.leibniz,map_sub,derivative_C,derivative_X,
    derivative_pow,smul_eq_mul,mul_zero,zero_add,mul_one]
  linear_combination -C (Polynomial.C m⁻¹)*C Polynomial.X*X^2*hc

 theorem dowlingLeadingLog_lambert_top (m : ℝ) (k : ℕ) :
    (2*k+3 : ℝ)*(coeff (2*k+3) ((dowlingLeadingLog m).subst dowlingLambertInverse)).coeff (k+1)=
      m⁻¹*(((2*k+3 : ℝ)/2)^(k+1)/(k+1).factorial-
        ((2*k+3 : ℝ)/2)^k/k.factorial) := by
  have h := dowlingLambert_lagrange (dowlingLeadingLog m) (2*k+3)
  rw [derivative_dowlingLeadingLog,dowlingQuadraticExp_power] at h
  have he : (X*(C (Polynomial.C m⁻¹)*(1-C Polynomial.X*X^2)))*
      dowlingQuadraticExp ((2*k+3 : ℝ)/2)=
      C (Polynomial.C m⁻¹)*(X*dowlingQuadraticExp ((2*k+3 : ℝ)/2)-
        C Polynomial.X*(X^3*dowlingQuadraticExp ((2*k+3 : ℝ)/2))) := by ring
  push_cast at h
  rw [he,coeff_C_mul,map_sub,coeff_succ_X_mul,coeff_C_mul,
    coeff_X_pow_mul',ite_eq_left (by omega)] at h
  rw [show 2*k+3-3=2*k by omega,
    show 2*k+2=2*(k+1) by omega] at h
  rw [dowlingQuadraticExp_coeff_even,dowlingQuadraticExp_coeff_even] at h
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff (k+1)) h
  have hcast : (2*k+3 : Polynomial ℝ)=Polynomial.C (2*k+3 : ℝ) := by
    symm
    exact_mod_cast (map_natCast (Polynomial.C : ℝ →+* Polynomial ℝ) (2*k+3) : Polynomial.C ((2*k+3 : ℕ) : ℝ)=((2*k+3 : ℕ) : Polynomial ℝ))
  rw [hcast,Polynomial.coeff_C_mul,Polynomial.coeff_C_mul,Polynomial.coeff_sub] at hc
  simp only [Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,ite_true,mul_one,
    Polynomial.coeff_X_mul] at hc
  exact hc

theorem dowlingLeading_factorial_difference (k : ℕ) :
    ((2*k+3 : ℝ)/2)^(k+1)/(k+1).factorial-((2*k+3 : ℝ)/2)^k/k.factorial=
      ((2*k+3 : ℝ)/2)^k/(2*(k+1).factorial) := by
  have hf : (k.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  field_simp
  ring

 theorem dowlingPCandidate_top_scaled_lambert (m : ℝ) (k : ℕ) :
    (coeff (2*k+3) (dowlingPCandidate m)).coeff (k+1)=
      m^(2*k+3)*(coeff (2*k+3)
        ((dowlingLeadingLog m).subst dowlingLambertInverse)).coeff (k+1) := by
  rw [dowlingPCandidate_odd_top_reduction]
  have hs : HasSubst (C (Polynomial.C m)*(X : PowerSeries (Polynomial ℝ))) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  rw [← subst_comp_subst_apply
    (HasSubst.of_constantCoeff_zero' dowlingLambertInverse_constantCoeff) hs,
    ← smul_eq_C_mul,← rescale_eq_subst,coeff_rescale,← map_pow,Polynomial.coeff_C_mul]

/-- Exact odd-rank top coefficient in the exponential generating normalization. -/
theorem dowlingPCandidate_odd_top (m : ℝ) (hm : m≠0) (k : ℕ) :
    ((2*k+3).factorial : ℝ)*(coeff (2*k+3) (dowlingPCandidate m)).coeff (k+1)=
      m^(2*k+2)*((2*k+1).doubleFactorial : ℝ)*(2*k+3 : ℝ)^k := by
  rw [dowlingPCandidate_top_scaled_lambert]
  have htop := dowlingLeadingLog_lambert_top m k
  rw [dowlingLeading_factorial_difference] at htop
  have hfact : ((2*k+3).factorial : ℝ)=
      (2*k+3 : ℝ)*(2^(k+1)*(k+1).factorial*((2*k+1).doubleFactorial : ℝ)) := by
    have h := Nat.factorial_eq_mul_doubleFactorial (2*k+1)
    rw [show 2*k+1+1=2*(k+1) by omega,Nat.doubleFactorial_two_mul] at h
    have hs := Nat.factorial_succ (2*k+2)
    rw [show 2*k+2=2*(k+1) by omega,h] at hs
    exact_mod_cast hs
  rw [hfact]
  calc
    _ = (2^(k+1)*(k+1).factorial*((2*k+1).doubleFactorial : ℝ))*
        m^(2*k+3)*((2*k+3 : ℝ)*
          (coeff (2*k+3) ((dowlingLeadingLog m).subst dowlingLambertInverse)).coeff (k+1)) := by ring
    _ = _ := by
      rw [htop,show 2*k+3=(2*k+2)+1 by omega,pow_succ m,div_pow,pow_succ (2 : ℝ)]
      have hf : ((k+1).factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (k+1)
      field_simp [hm]

end Dowling
