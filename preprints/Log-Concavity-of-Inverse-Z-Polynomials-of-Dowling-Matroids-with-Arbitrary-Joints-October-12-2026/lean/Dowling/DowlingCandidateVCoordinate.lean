import Dowling.DowlingCandidateExponentSupport

noncomputable section
namespace Dowling
open PowerSeries

/-- `exp(v)-1`, before adjoining the polynomial parameter. -/
def candidateUReal : PowerSeries ℝ := exp ℝ - 1
/-- `exp(v)-1-v`. -/
def candidateHReal : PowerSeries ℝ := exp ℝ - 1 - X
/-- `(exp(v)-1)/v`, with its removable constant term filled in. -/
def candidateExpTailReal : PowerSeries ℝ := mk fun n => ((n+1).factorial : ℝ)⁻¹

def candidateU : PowerSeries (Polynomial ℝ) := PowerSeries.map Polynomial.C candidateUReal
def candidateH : PowerSeries (Polynomial ℝ) := PowerSeries.map Polynomial.C candidateHReal

def candidateNegativeTH : PowerSeries (Polynomial ℝ) := -C Polynomial.X*candidateH

/-- Division-free form of
`((1+t(exp(v)-1))*exp(-t(exp(v)-1-v))-1)/t`. -/
def dowlingVCoordinate : PowerSeries (Polynomial ℝ) :=
  candidateU * (exp (Polynomial ℝ)).subst candidateNegativeTH -
    candidateH * (PowerSeries.map Polynomial.C candidateExpTailReal).subst candidateNegativeTH

theorem candidateU_weight : CandidateWeight 1 candidateU := by
  apply candidateWeight_realSeries
  intro n hn
  have : n=0 := by omega
  subst n
  simp [candidateUReal]

theorem candidateH_weight : CandidateWeight 2 candidateH := by
  apply candidateWeight_realSeries
  intro n hn
  interval_cases n <;> norm_num [candidateHReal,coeff_exp]

@[simp] theorem candidateU_constantCoeff : candidateU.constantCoeff=0 :=
  candidateU_weight.constantCoeff_eq_zero (by omega)
@[simp] theorem candidateH_constantCoeff : candidateH.constantCoeff=0 :=
  candidateH_weight.constantCoeff_eq_zero (by omega)

@[simp] theorem candidateNegativeTH_constantCoeff : candidateNegativeTH.constantCoeff=0 := by
  simp [candidateNegativeTH]

theorem candidateNegativeTH_weight : CandidateWeight 0 candidateNegativeTH := by
  simpa only [candidateNegativeTH,zero_add,neg_mul] using candidateH_weight.parameter_mul.neg

theorem dowlingVCoordinate_weight : CandidateWeight 1 dowlingVCoordinate := by
  have he := candidateNegativeTH_weight.exp candidateNegativeTH_constantCoeff
  have ht := candidateWeight_realSeries_subst (v := 0) candidateExpTailReal
    (by intro d hd; omega) candidateNegativeTH_weight candidateNegativeTH_constantCoeff
  have hleft : CandidateWeight 1 (candidateU * (exp (Polynomial ℝ)).subst candidateNegativeTH) := by
    simpa only [add_zero] using candidateU_weight.mul he
  have hright : CandidateWeight 2 (candidateH * (PowerSeries.map Polynomial.C candidateExpTailReal).subst candidateNegativeTH) := by
    simpa only [zero_mul,add_zero] using candidateH_weight.mul ht
  exact hleft.sub (hright.mono (by omega))

@[simp] theorem dowlingVCoordinate_constantCoeff : dowlingVCoordinate.constantCoeff=0 :=
  dowlingVCoordinate_weight.constantCoeff_eq_zero (by omega)

@[simp] theorem candidateU_coeff_one : coeff 1 candidateU=1 := by
  norm_num [candidateU,candidateUReal,coeff_map,coeff_exp]
@[simp] theorem candidateH_coeff_one : coeff 1 candidateH=0 := by
  norm_num [candidateH,candidateHReal,coeff_map,coeff_exp]

@[simp] theorem dowlingVCoordinate_coeff_one : coeff 1 dowlingVCoordinate=1 := by
  have he : ((exp (Polynomial ℝ)).subst candidateNegativeTH).constantCoeff=1 := by
    rw [constantCoeff_subst_of_constantCoeff_zero candidateNegativeTH_constantCoeff]
    exact constantCoeff_exp
  rw [← PowerSeries.constantCoeff_eq] at he
  simp only [dowlingVCoordinate,map_sub,coeff_one_mul,candidateU_constantCoeff,
    candidateH_constantCoeff,candidateU_coeff_one,candidateH_coeff_one,he,
    zero_mul,mul_zero,one_mul,add_zero,sub_zero]

/-- The strict-support coordinate used to identify the actual KL series. -/
def dowlingVInverse : PowerSeries (Polynomial ℝ) :=
  dowlingVCoordinate.substInvOfIsUnit (by simp)

theorem dowlingVInverse_weight : CandidateWeight 1 dowlingVInverse :=
  dowlingVCoordinate_weight.substInvOfIsUnit dowlingVCoordinate_coeff_one _

@[simp] theorem dowlingVInverse_constantCoeff : dowlingVInverse.constantCoeff=0 :=
  dowlingVInverse_weight.constantCoeff_eq_zero (by omega)

theorem dowlingVCoordinate_subst_inverse : dowlingVCoordinate.subst dowlingVInverse=X :=
  subst_substInvOfIsUnit_right _ dowlingVCoordinate_constantCoeff _

theorem dowlingVInverse_subst_coordinate : dowlingVInverse.subst dowlingVCoordinate=X :=
  subst_substInvOfIsUnit_left _ dowlingVCoordinate_constantCoeff _

end Dowling
