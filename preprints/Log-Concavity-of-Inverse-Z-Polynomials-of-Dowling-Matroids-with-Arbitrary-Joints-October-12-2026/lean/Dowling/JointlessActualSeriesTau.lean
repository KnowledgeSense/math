import Dowling.RetainedNontrivialIdentity
import Dowling.DowlingLeadingRankOne
import Dowling.DowlingInverseZCandidateExpansion

noncomputable section
namespace Dowling
open PowerSeries

/-- The actual odd KL leading-coefficient primitive in Lambert coordinates. -/
def jointTauSeries (m : ℝ) : PowerSeries (Polynomial ℝ) :=
  C Polynomial.X*(dowlingLeadingLog m).subst
    (dowlingLambertInverse.subst (C (Polynomial.C m)*X))

theorem leadingLambert_lagrange_succ (m : ℝ) (n : ℕ) :
    Polynomial.C (n+1 : ℝ)*coeff (n+1) ((dowlingLeadingLog m).subst dowlingLambertInverse)=
      Polynomial.C m⁻¹*coeff n (dowlingCorrectedQuadratic ((n+1 : ℝ)/2)) := by
  have h := dowlingLambert_lagrange (dowlingLeadingLog m) (n+1)
  rw [derivative_dowlingLeadingLog,dowlingQuadraticExp_power] at h
  have he : (X*(C (Polynomial.C m⁻¹)*(1-C Polynomial.X*X^2)))*
      dowlingQuadraticExp (((n+1 : ℕ) : ℝ)/2)=
      C (Polynomial.C m⁻¹)*X*dowlingCorrectedQuadratic (((n+1 : ℕ) : ℝ)/2) := by
    dsimp [dowlingCorrectedQuadratic]
    ring
  rw [he,mul_assoc,coeff_C_mul,coeff_succ_X_mul] at h
  simpa only [Nat.cast_add,Nat.cast_one,map_add,map_natCast,map_one] using h

theorem leadingLambert_coeff_succ (m : ℝ) (n : ℕ) :
    coeff (n+1) ((dowlingLeadingLog m).subst dowlingLambertInverse)=
      Polynomial.C (m⁻¹/(n+1))*coeff n (dowlingCorrectedQuadratic ((n+1 : ℝ)/2)) := by
  have hn : (n+1 : ℝ)≠0 := by positivity
  apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hn)
  rw [leadingLambert_lagrange_succ,← mul_assoc,← map_mul]
  congr 2
  field_simp

theorem leadingLambert_coeff_even (m : ℝ) (k : ℕ) :
    coeff (2*k) ((dowlingLeadingLog m).subst dowlingLambertInverse)=0 := by
  cases k with
  | zero =>
    rw [Nat.mul_zero,coeff_zero_eq_constantCoeff_apply,
      candidate_subst_constantCoeff _ _ dowlingLambertInverse_constantCoeff]
    simp [dowlingLeadingLog]
  | succ k =>
    rw [show 2*(k+1)=(2*k+1)+1 by omega,leadingLambert_coeff_succ,
      dowlingCorrectedQuadratic_coeff_odd,mul_zero]

theorem leadingLambert_coeff_odd (m : ℝ) (k : ℕ) :
    coeff (2*k+1) ((dowlingLeadingLog m).subst dowlingLambertInverse)=
      Polynomial.C (m⁻¹/(2*k+1)*dowlingQuadraticWeight ((2*k+1 : ℝ)/2) k)*Polynomial.X^k := by
  rw [leadingLambert_coeff_succ,dowlingCorrectedQuadratic_coeff_even,← mul_assoc,← map_mul]
  push_cast
  rfl

end Dowling
