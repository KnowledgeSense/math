import Dowling.DowlingCandidateZRelation

noncomputable section
namespace Dowling
open PowerSeries

/-- Evaluation of the polynomial parameter, leaving the outer formal variable. -/
def candidateEval (t : ℝ) : PowerSeries (Polynomial ℝ) →+* PowerSeries ℝ :=
  PowerSeries.map (Polynomial.evalRingHom t)

@[simp] theorem candidateEval_coeff (t : ℝ) (f : PowerSeries (Polynomial ℝ)) (n : ℕ) :
    coeff n (candidateEval t f)=(coeff n f).eval t := by
  simp [candidateEval]

 theorem candidateEval_derivative (t : ℝ) (f : PowerSeries (Polynomial ℝ)) :
    candidateEval t (derivative f)=derivative (candidateEval t f) := by
  apply PowerSeries.ext
  intro n
  simp [coeff_derivative,candidateEval_coeff]

 theorem candidateEval_subst (t : ℝ) (f g : PowerSeries (Polynomial ℝ))
    (hg : g.constantCoeff=0) :
    candidateEval t (f.subst g)=(candidateEval t f).subst (candidateEval t g) := by
  exact map_subst (HasSubst.of_constantCoeff_zero' hg) f

@[simp] theorem candidateEval_constantCoeff (t : ℝ) (f : PowerSeries (Polynomial ℝ)) :
    PowerSeries.constantCoeff (candidateEval t f)=f.constantCoeff.eval t := by
  rw [← coeff_zero_eq_constantCoeff_apply,candidateEval_coeff,coeff_zero_eq_constantCoeff_apply]

 theorem candidateEval_exp (t : ℝ) (f : PowerSeries (Polynomial ℝ))
    (hf : f.constantCoeff=0) : candidateEval t (candidateExp f)=candidateExp (candidateEval t f) := by
  rw [candidateExp,candidateEval_subst t _ _ hf]
  congr 1
  exact PowerSeries.map_exp _

 theorem candidateEval_C (t : ℝ) (p : Polynomial ℝ) : candidateEval t (C p)=C (p.eval t) := by
  exact map_C _ _

@[simp] theorem candidateEval_X (t : ℝ) : candidateEval t X=X := by
  exact map_X _

 theorem candidateEval_log_reciprocal (t : ℝ) (ht : t≠0) :
    (candidateEval t⁻¹ dowlingLogCoordinate).subst (C t*X)=
      C t*candidateEval t dowlingLogCoordinate := by
  apply PowerSeries.ext
  intro n
  rw [← smul_eq_C_mul,← rescale_eq_subst,coeff_rescale,coeff_C_mul,
    candidateEval_coeff,candidateEval_coeff]
  by_cases hn : n=0
  · subst n
    simp [dowlingLogCoordinate]
  · have hp : t*t^(n-1)=t^n := by
      rw [← pow_succ',Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
    have hinv : t^(n-1)*(t⁻¹)^(n-1)=1 := by rw [← mul_pow,mul_inv_cancel₀ ht,one_pow]
    simp only [dowlingLogCoordinate,coeff_mk,ite_eq_right hn,Polynomial.eval_sub,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_one]
    split_ifs with hn1
    · subst n
      norm_num
    · simp only [Polynomial.eval_zero,sub_zero]
      rw [← hp]
      linear_combination ((-1 : ℝ)^(n+1)/n)*t*hinv

end Dowling
