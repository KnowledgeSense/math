import Dowling.DowlingCandidateLogarithm

noncomputable section
namespace Dowling
open PowerSeries

 theorem candidateU_eq_exp_sub_one : candidateU=exp (Polynomial ℝ)-1 := by
  simp only [candidateU,candidateUReal,map_sub,map_exp,map_one]

theorem candidateH_eq : candidateH=candidateU-X := by
  simp only [candidateH,candidateHReal,candidateU,candidateUReal,map_sub,map_X]

theorem candidateK_eq : candidateK=candidateH-C (Polynomial.C (1/2 : ℝ))*candidateU^2 := by
  simp only [candidateK,candidateKReal,map_sub,map_mul,map_pow,map_C,candidateH,candidateU]

theorem candidateExpTail_identity :
    X*(PowerSeries.map Polynomial.C candidateExpTailReal)=candidateU := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [candidateU_eq_exp_sub_one]
  | succ n =>
    simp [coeff_succ_X_mul,coeff_map,candidateExpTailReal,candidateU_eq_exp_sub_one,coeff_exp,one_div]

theorem candidateExpTail_subst {g : PowerSeries (Polynomial ℝ)} (hg : g.constantCoeff=0) :
    g*(PowerSeries.map Polynomial.C candidateExpTailReal).subst g=candidateExp g-1 := by
  have hs := HasSubst.of_constantCoeff_zero' hg
  have h := congrArg (substAlgHom (R := Polynomial ℝ) hs) candidateExpTail_identity
  rw [candidateU_eq_exp_sub_one] at h
  simpa only [map_mul,map_sub,map_one,substAlgHom_X,coe_substAlgHom,candidateExp] using h

theorem dowlingVCoordinate_cleared : C Polynomial.X*dowlingVCoordinate=
    (1+C Polynomial.X*candidateU)*candidateExp candidateNegativeTH-1 := by
  have ht := candidateExpTail_subst candidateNegativeTH_constantCoeff
  change (-C Polynomial.X*candidateH)*
    (PowerSeries.map Polynomial.C candidateExpTailReal).subst candidateNegativeTH =
      candidateExp candidateNegativeTH-1 at ht
  unfold dowlingVCoordinate
  change C Polynomial.X*(candidateU*candidateExp candidateNegativeTH-
    candidateH*(PowerSeries.map Polynomial.C candidateExpTailReal).subst candidateNegativeTH)=_
  linear_combination ht

 theorem candidate_log_subst_U : (log (Polynomial ℝ)).subst candidateU=X := by
  rw [candidateU_eq_exp_sub_one]
  exact subst_log_exp_sub_one _

 theorem candidateExp_log_subst {g : PowerSeries (Polynomial ℝ)} (hg : g.constantCoeff=0) :
    candidateExp ((log (Polynomial ℝ)).subst g)=1+g := by
  rw [← candidateExp_subst constantCoeff_log hg]
  change PowerSeries.subst g ((exp (Polynomial ℝ)).subst (log (Polynomial ℝ)))=1+g
  rw [subst_exp_log]
  have hs := HasSubst.of_constantCoeff_zero' hg
  rw [← coe_substAlgHom hs,map_add,map_one,substAlgHom_X]

def candidateGofU : PowerSeries (Polynomial ℝ) := dowlingLogCoordinate.subst candidateU

 theorem candidateGofU_log_identity : C Polynomial.X*candidateGofU=
    (log (Polynomial ℝ)).subst (C Polynomial.X*candidateU)+candidateNegativeTH := by
  have hs := HasSubst.of_constantCoeff_zero' candidateU_constantCoeff
  have h := congrArg (substAlgHom (R := Polynomial ℝ) hs) dowlingLogCoordinate_log_identity
  simp only [map_mul,map_add,map_sub,substAlgHom_X,coe_substAlgHom,subst_C] at h
  rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (by simp)) hs] at h
  have hinner : (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))).subst candidateU=
      C Polynomial.X*candidateU := by
    rw [← coe_substAlgHom hs,map_mul,substAlgHom_X,coe_substAlgHom,subst_C]
    rfl
  rw [hinner] at h
  rw [candidate_log_subst_U] at h
  change C Polynomial.X*candidateGofU=
    (log (Polynomial ℝ)).subst (C Polynomial.X*candidateU)+C Polynomial.X*X-
      C Polynomial.X*candidateU at h
  rw [h,candidateNegativeTH,candidateH_eq]
  ring

@[simp] theorem candidateGofU_constantCoeff : candidateGofU.constantCoeff=0 := by
  rw [PowerSeries.constantCoeff_eq,candidateGofU,constantCoeff_subst_of_constantCoeff_zero candidateU_constantCoeff]
  exact dowlingLogCoordinate_constantCoeff

 theorem candidateGofU_exponential : candidateExp (C Polynomial.X*candidateGofU)=
    1+C Polynomial.X*dowlingVCoordinate := by
  have ht : (C Polynomial.X*candidateU).constantCoeff=0 := by simp
  have hl : PowerSeries.constantCoeff ((log (Polynomial ℝ)).subst
      (C Polynomial.X*candidateU))=0 := by
    rw [PowerSeries.constantCoeff_eq,constantCoeff_subst_of_constantCoeff_zero ht]
    exact constantCoeff_log
  rw [candidateGofU_log_identity,candidateExp_add hl candidateNegativeTH_constantCoeff,
    candidateExp_log_subst ht]
  rw [dowlingVCoordinate_cleared]
  ring

theorem braidLogZCandidate_subst_GofU : braidLogZCandidate.subst candidateGofU =
    C Polynomial.X*candidateGofU + (X+C Polynomial.X*candidateK) := by
  have hs := HasSubst.of_constantCoeff_zero' candidateU_constantCoeff
  have hg := HasSubst.of_constantCoeff_zero' dowlingLogCoordinate_constantCoeff
  rw [candidateGofU,← subst_comp_subst_apply hg hs,
    braidLogZCandidate_subst_coordinate]
  have hlog : PowerSeries.subst candidateU
      ((log (Polynomial ℝ)).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ)))) =
        (log (Polynomial ℝ)).subst (C Polynomial.X*candidateU) := by
    rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (by simp)) hs]
    congr 1
    rw [← coe_substAlgHom hs,map_mul,substAlgHom_X,coe_substAlgHom,subst_C]
    rfl
  unfold candidateLogZInU
  rw [← coe_substAlgHom hs,map_sub,map_add,map_mul,map_mul,map_pow,substAlgHom_X]
  simp only [coe_substAlgHom,subst_C,candidate_log_subst_U,hlog]
  change X+(log (Polynomial ℝ)).subst (C Polynomial.X*candidateU)-
    C (Polynomial.C (1/2 : ℝ))*C Polynomial.X*candidateU^2 =
      C Polynomial.X*candidateGofU+(X+C Polynomial.X*candidateK)
  rw [candidateGofU_log_identity,candidateK_eq,candidateNegativeTH]
  ring

end Dowling
