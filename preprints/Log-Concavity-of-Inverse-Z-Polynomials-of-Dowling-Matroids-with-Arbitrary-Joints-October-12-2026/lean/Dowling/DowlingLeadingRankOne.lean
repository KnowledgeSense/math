import Dowling.DowlingLeadingActual

noncomputable section
namespace Dowling
open PowerSeries

 theorem dowlingLeadingLog_lambert_linear (m : ℝ) :
    coeff 1 ((dowlingLeadingLog m).subst dowlingLambertInverse)=Polynomial.C m⁻¹ := by
  have h := dowlingLambert_lagrange (dowlingLeadingLog m) 1
  simp only [Nat.cast_one,one_mul,pow_one,derivative_dowlingLeadingLog] at h
  rw [mul_assoc,coeff_succ_X_mul,coeff_zero_eq_constantCoeff_apply] at h
  have he := candidateExp_constantCoeff
    (show (-dowlingQuadraticExponent).constantCoeff=0 by simp)
  simpa only [map_mul,map_sub,map_one,constantCoeff_C,constantCoeff_X,map_pow,
    zero_pow (by omega : 2≠0),mul_zero,sub_zero,mul_one,he] using h

 theorem dowlingPCandidate_coeff_one (m : ℝ) (hm : m≠0) :
    coeff 1 (dowlingPCandidate m)=1 := by
  let q : PowerSeries (Polynomial ℝ) := dowlingLambertInverse.subst (C (Polynomial.C m)*X)
  have hd : coeff 1 (dowlingPCandidate m)-coeff 1 ((dowlingLeadingLog m).subst q)=0 := by
    apply Polynomial.ext
    intro k
    have h := dowlingPCandidate_leading_difference m 1 k (by omega)
    simpa only [map_sub,coeff_one,ite_eq_right (by omega : 1≠0),sub_zero,
      Polynomial.coeff_sub,Polynomial.coeff_zero] using h
  rw [sub_eq_zero] at hd
  rw [hd]
  have hs : HasSubst (C (Polynomial.C m)*(X : PowerSeries (Polynomial ℝ))) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  dsimp only [q]
  rw [← subst_comp_subst_apply
    (HasSubst.of_constantCoeff_zero' dowlingLambertInverse_constantCoeff) hs,
    ← smul_eq_C_mul,← rescale_eq_subst,coeff_rescale,pow_one,
    dowlingLeadingLog_lambert_linear,← map_mul,mul_inv_cancel₀ hm,map_one]

 theorem fullP_one (G : Type*) [Group G] [Fintype G] : fullP G 1=1 := by
  have h := congrArg (coeff 1) (fullPSeries_eq_candidate (G := G))
  rw [dowlingPCandidate_coeff_one _ (by exact_mod_cast Fintype.card_ne_zero (α := G))] at h
  change coeff 1 (invariantEGF (fullP G))=1 at h
  rw [invariantEGF_coeff] at h
  norm_num at h
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  simpa only [Polynomial.map_one] using h

end Dowling
