import Dowling.JointlessActualSeriesTau

noncomputable section
namespace Dowling
open PowerSeries

def jointLeadingSeries (m : ℝ) : PowerSeries (Polynomial ℝ) :=
  (dowlingLeadingLog m).subst (dowlingLambertInverse.subst (C (Polynomial.C m)*X))

theorem jointLeadingSeries_coeff (m : ℝ) (n : ℕ) :
    coeff n (jointLeadingSeries m)=Polynomial.C (m^n)*
      coeff n ((dowlingLeadingLog m).subst dowlingLambertInverse) := by
  rw [jointLeadingSeries,← subst_comp_subst_apply
    (HasSubst.of_constantCoeff_zero' dowlingLambertInverse_constantCoeff)
    (HasSubst.of_constantCoeff_zero' (by simp)),
    ← smul_eq_C_mul,← rescale_eq_subst,coeff_rescale,← map_pow]

theorem jointTauSeries_coeff_even (m : ℝ) (k : ℕ) : coeff (2*k) (jointTauSeries m)=0 := by
  change coeff (2*k) (C Polynomial.X*jointLeadingSeries m)=0
  rw [coeff_C_mul,jointLeadingSeries_coeff,leadingLambert_coeff_even,mul_zero,mul_zero]

theorem jointLeadingSeries_coeff_odd_monomial (m : ℝ) (k : ℕ) :
    coeff (2*k+1) (jointLeadingSeries m)=
      Polynomial.C ((coeff (2*k+1) (jointLeadingSeries m)).coeff k)*Polynomial.X^k := by
  rw [jointLeadingSeries_coeff,leadingLambert_coeff_odd]
  simp only [Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,ite_true,mul_one]
  rw [← mul_assoc,← map_mul]

variable (G : Type*) [Group G] [Fintype G]

theorem jointLeadingSeries_actual_top (k : ℕ) :
    (coeff (2*k+1) (jointLeadingSeries (Fintype.card G))).coeff k=
      ((2*k+1).factorial : ℝ)⁻¹*((fullP G (2*k+1)).coeff k : ℝ) := by
  have h := dowlingPCandidate_leading_difference (Fintype.card G) (2*k+1) k (by omega)
  change ((coeff (2*k+1) (dowlingPCandidate (Fintype.card G)-1-jointLeadingSeries (Fintype.card G))).coeff k)=0 at h
  simp only [map_sub,coeff_one,ite_eq_right (by omega : 2*k+1≠0),sub_zero,
    Polynomial.coeff_sub,sub_eq_zero] at h
  rw [← fullPSeries_eq_candidate] at h
  change (coeff (2*k+1) (invariantEGF (fullP G))).coeff k=_ at h
  rw [invariantEGF_coeff,Polynomial.coeff_C_mul,Polynomial.coeff_map] at h
  exact h.symm

/-- Every primitive coefficient is the actual odd-rank KL top coefficient,
including rank one and zero even coefficients. -/
theorem jointTauSeries_coeff_odd (k : ℕ) :
    coeff (2*k+1) (jointTauSeries (Fintype.card G))=
      Polynomial.C (((2*k+1).factorial : ℝ)⁻¹*((fullP G (2*k+1)).coeff k : ℝ))*Polynomial.X^(k+1) := by
  change coeff (2*k+1) (C Polynomial.X*jointLeadingSeries (Fintype.card G))=_
  rw [coeff_C_mul,jointLeadingSeries_coeff_odd_monomial,jointLeadingSeries_actual_top]
  ring

end Dowling
