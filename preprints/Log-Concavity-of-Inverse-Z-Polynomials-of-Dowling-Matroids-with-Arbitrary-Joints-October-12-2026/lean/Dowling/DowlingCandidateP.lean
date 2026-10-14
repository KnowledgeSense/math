import Dowling.DowlingCandidateVCoordinate

noncomputable section
namespace Dowling
open PowerSeries

/-- The real series `exp(v)-1-v-(exp(v)-1)^2/2` starts in degree three. -/
def candidateKReal : PowerSeries ℝ :=
  candidateHReal - C (1/2 : ℝ) * candidateUReal^2

def candidateK : PowerSeries (Polynomial ℝ) := PowerSeries.map Polynomial.C candidateKReal

theorem candidateK_weight : CandidateWeight 3 candidateK := by
  apply candidateWeight_realSeries
  intro n hn
  interval_cases n <;>
    norm_num [candidateKReal,candidateHReal,candidateUReal,pow_two,coeff_C_mul,coeff_X,coeff_mul,
      Finset.Nat.antidiagonal_succ,Finset.Nat.antidiagonal_zero,coeff_exp]

def dowlingPLogV (m : ℝ) : PowerSeries (Polynomial ℝ) :=
  C (Polynomial.C m⁻¹) * (X + C Polynomial.X * candidateK)

def dowlingPCandidate (m : ℝ) : PowerSeries (Polynomial ℝ) :=
  PowerSeries.subst (dowlingVInverse.subst (C (Polynomial.C m)*X))
    ((exp (Polynomial ℝ)).subst (dowlingPLogV m))

theorem candidateWeight_X : CandidateWeight 1 (X : PowerSeries (Polynomial ℝ)) := by
  simpa only [map_X] using candidateWeight_realSeries (w := 1)
    (X : PowerSeries ℝ) (by
      intro n hn
      have : n=0 := by omega
      subst n
      simp)

theorem dowlingPLogV_weight (m : ℝ) : CandidateWeight 1 (dowlingPLogV m) := by
  exact (candidateWeight_X.add candidateK_weight.parameter_mul).scalar_mul m⁻¹

@[simp] theorem dowlingPLogV_constantCoeff (m : ℝ) : (dowlingPLogV m).constantCoeff=0 :=
  (dowlingPLogV_weight m).constantCoeff_eq_zero (by omega)

theorem dowlingPCandidate_sub_one_weight (m : ℝ) :
    CandidateWeight 1 (dowlingPCandidate m-1) := by
  have hg := dowlingVInverse_weight.subst (candidateWeight_X.scalar_mul m)
  have hs := HasSubst.of_constantCoeff_zero' (hg.constantCoeff_eq_zero (by omega))
  have h := ((dowlingPLogV_weight m).exp_sub_one).subst hg
  rw [← coe_substAlgHom hs, map_sub, map_one, coe_substAlgHom] at h
  exact h

/-- The candidate satisfies the full strict half-rank support condition. -/
theorem dowlingPCandidate_high_coeff (m : ℝ) (n k : ℕ) (hn : 0<n) (hk : n≤2*k) :
    (coeff n (dowlingPCandidate m)).coeff k = 0 := by
  have h := dowlingPCandidate_sub_one_weight m n k (by omega)
  simpa only [map_sub,coeff_one,ite_eq_right (Nat.ne_of_gt hn),sub_zero] using h

@[simp] theorem dowlingPCandidate_constantCoeff (m : ℝ) :
    (dowlingPCandidate m).constantCoeff=1 := by
  have h := (dowlingPCandidate_sub_one_weight m).constantCoeff_eq_zero (by omega)
  simpa only [map_sub,map_one,sub_eq_zero] using h

end Dowling
