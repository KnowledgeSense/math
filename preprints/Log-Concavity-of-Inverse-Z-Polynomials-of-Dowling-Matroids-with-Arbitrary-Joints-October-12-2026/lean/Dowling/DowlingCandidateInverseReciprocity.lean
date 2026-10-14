import Dowling.DowlingCandidateEvaluation

noncomputable section
namespace Dowling
open PowerSeries

theorem candidate_real_subst_constantCoeff (f g : PowerSeries ℝ)
    (hg : g.constantCoeff=0) : PowerSeries.constantCoeff (f.subst g)=f.constantCoeff := by
  rw [PowerSeries.constantCoeff_eq,constantCoeff_subst_of_constantCoeff_zero hg]
  rfl

 theorem candidate_real_subst_C_mul {f g : PowerSeries ℝ} (hg : g.constantCoeff=0) (c : ℝ) :
    (C c*f).subst g=C c*(f.subst g) := by
  have hs := HasSubst.of_constantCoeff_zero' hg
  rw [← coe_substAlgHom hs,map_mul,coe_substAlgHom,subst_C]
  rfl

 theorem candidate_real_subst_rescale (f : PowerSeries ℝ) {g : PowerSeries ℝ}
    (hg : g.constantCoeff=0) (c : ℝ) :
    PowerSeries.subst g (f.subst (C c*X))=f.subst (C c*g) := by
  rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (by simp))
    (HasSubst.of_constantCoeff_zero' hg),candidate_real_subst_C_mul hg,
    subst_X (HasSubst.of_constantCoeff_zero' hg)]

 theorem candidateEval_inverse_right (t : ℝ) :
    (candidateEval t dowlingLogCoordinate).subst (candidateEval t dowlingLogInverse)=X := by
  have h := congrArg (candidateEval t) dowlingLogCoordinate_subst_inverse
  rw [candidateEval_subst _ _ _ dowlingLogInverse_constantCoeff,candidateEval_X] at h
  exact h

 theorem candidateEval_inverse_left (t : ℝ) :
    (candidateEval t dowlingLogInverse).subst (candidateEval t dowlingLogCoordinate)=X := by
  have h := congrArg (candidateEval t) dowlingLogInverse_subst_coordinate
  rw [candidateEval_subst _ _ _ dowlingLogCoordinate_constantCoeff,candidateEval_X] at h
  exact h

 theorem candidateEval_logInverse_reciprocal (t : ℝ) (ht : t≠0) :
    (candidateEval t⁻¹ dowlingLogInverse).subst (C t*X)=
      C t*candidateEval t dowlingLogInverse := by
  let f := candidateEval t⁻¹ dowlingLogCoordinate
  let a : PowerSeries ℝ := (candidateEval t⁻¹ dowlingLogInverse).subst (C t*X)
  let b : PowerSeries ℝ := C t*candidateEval t dowlingLogInverse
  have hf0 : f.constantCoeff=0 := by simp [f]
  have htX : HasSubst (C t*(X : PowerSeries ℝ)) := HasSubst.of_constantCoeff_zero' (by simp)
  have hi0 : PowerSeries.constantCoeff (candidateEval t⁻¹ dowlingLogInverse)=0 := by simp
  have hj0 : PowerSeries.constantCoeff (candidateEval t dowlingLogInverse)=0 := by simp
  have ha0 : PowerSeries.constantCoeff a=0 := by
    dsimp only [a]
    rw [candidate_real_subst_constantCoeff _ _ (by simp),hi0]
  have hb0 : b.constantCoeff=0 := by simp [b]
  have ha : f.subst a=C t*X := by
    dsimp only [f,a]
    rw [← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hi0) htX,
      candidateEval_inverse_right,subst_X htX]
  have hb : f.subst b=C t*X := by
    dsimp only [f,b]
    rw [← candidate_real_subst_rescale _ hj0,candidateEval_log_reciprocal t ht,
      candidate_real_subst_C_mul hj0,candidateEval_inverse_right]
  have he := congrArg (fun z : PowerSeries ℝ =>
      (candidateEval t⁻¹ dowlingLogInverse).subst z) (ha.trans hb.symm)
  rw [← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hf0)
      (HasSubst.of_constantCoeff_zero' ha0),
    ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hf0)
      (HasSubst.of_constantCoeff_zero' hb0)] at he
  change PowerSeries.subst a
    ((candidateEval t⁻¹ dowlingLogInverse).subst (candidateEval t⁻¹ dowlingLogCoordinate))=
    PowerSeries.subst b
    ((candidateEval t⁻¹ dowlingLogInverse).subst (candidateEval t⁻¹ dowlingLogCoordinate)) at he
  rw [candidateEval_inverse_left,subst_X (HasSubst.of_constantCoeff_zero' ha0),
    subst_X (HasSubst.of_constantCoeff_zero' hb0)] at he
  exact he

end Dowling
