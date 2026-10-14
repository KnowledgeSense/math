import Dowling.DowlingLeadingCongruence

noncomputable section
namespace Dowling
open PowerSeries Finset

 theorem candidateWeight_pow_difference_zero {w : ℕ} {f g : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight 0 f) (hg : CandidateWeight 0 g)
    (hd : CandidateWeight w (f-g)) (d : ℕ) : CandidateWeight w (f^d-g^d) := by
  induction d with
  | zero => simpa only [pow_zero,sub_self] using candidateWeight_zero w
  | succ d ih =>
    have he : f^(d+1)-g^(d+1)=(f^d-g^d)*f+g^d*(f-g) := by ring
    rw [he]
    have hl : CandidateWeight w ((f^d-g^d)*f) := by simpa using ih.mul hf
    have hr : CandidateWeight w (g^d*(f-g)) := by simpa using (hg.pow d).mul hd
    exact hl.add hr

 theorem candidateWeight_exp_difference {w : ℕ} {f g : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight 0 f) (hg : CandidateWeight 0 g)
    (hf0 : f.constantCoeff=0) (hg0 : g.constantCoeff=0)
    (hd : CandidateWeight w (f-g)) : CandidateWeight w (candidateExp f-candidateExp g) := by
  intro n k hn
  rw [map_sub,candidateExp,candidateExp,candidate_coeff_subst _ _ hf0,
    candidate_coeff_subst _ _ hg0,← sum_sub_distrib]
  simp only [← mul_sub,← map_sub,Polynomial.finsetSum_coeff]
  apply sum_eq_zero
  intro d _
  have he : coeff d (exp (Polynomial ℝ))=Polynomial.C ((d.factorial : ℝ)⁻¹) := by
    simp [coeff_exp,one_div]
  rw [he,Polynomial.coeff_C_mul]
  rw [candidateWeight_pow_difference_zero hf hg hd d n k hn,mul_zero]

 theorem candidateWeight_exp_remainder {f : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight 1 f) : CandidateWeight 2 (candidateExp f-1-f) := by
  have h0 := hf.constantCoeff_eq_zero (by omega)
  have h := candidateWeight_realSeries_subst (v := 2) candidateHReal
    (by intro n hn; interval_cases n <;> norm_num [candidateHReal,coeff_exp]) hf h0
  have hs := HasSubst.of_constantCoeff_zero' h0
  change CandidateWeight 2 (candidateH.subst f) at h
  rw [candidateH_eq,candidateU_eq_exp_sub_one,← coe_substAlgHom hs,
    map_sub,map_sub,map_one,substAlgHom_X,coe_substAlgHom] at h
  exact h

end Dowling
