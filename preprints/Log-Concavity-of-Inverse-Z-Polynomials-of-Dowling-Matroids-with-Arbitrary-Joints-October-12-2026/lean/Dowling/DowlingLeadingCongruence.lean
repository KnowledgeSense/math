import Dowling.DowlingCandidateZRelation

noncomputable section
namespace Dowling
open PowerSeries Finset

 theorem candidateWeight_pow_difference {f g : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight 1 f) (hg : CandidateWeight 1 g)
    (hd : CandidateWeight 2 (f-g)) (d : ℕ) :
    CandidateWeight (d+1) (f^d-g^d) := by
  induction d with
  | zero => simpa only [pow_zero,sub_self] using candidateWeight_zero 1
  | succ d ih =>
    have he : f^(d+1)-g^(d+1)=(f^d-g^d)*f+g^d*(f-g) := by ring
    rw [he]
    have hl := ih.mul hf
    have hr := (hg.pow d).mul hd
    simpa only [mul_one,Nat.add_assoc] using hl.add (by simpa [Nat.add_assoc] using hr)

 theorem candidateWeight_subst_difference {h f g : PowerSeries (Polynomial ℝ)}
    (hh : CandidateWeight 1 h) (hf : CandidateWeight 1 f) (hg : CandidateWeight 1 g)
    (hd : CandidateWeight 2 (f-g)) :
    CandidateWeight 2 (h.subst f-h.subst g) := by
  intro n k hn
  rw [map_sub,candidate_coeff_subst _ _ (hf.constantCoeff_eq_zero (by omega)),
    candidate_coeff_subst _ _ (hg.constantCoeff_eq_zero (by omega)),← sum_sub_distrib]
  simp only [← mul_sub,← map_sub,Polynomial.finsetSum_coeff]
  apply sum_eq_zero
  intro d _
  rw [Polynomial.coeff_mul]
  apply sum_eq_zero
  intro ab hab
  have hab' := mem_antidiagonal.mp hab
  by_cases h : d < 2*ab.1+1
  · rw [hh d ab.1 h,zero_mul]
  · have hp := candidateWeight_pow_difference hf hg hd d
    rw [hp n ab.2 (by omega),mul_zero]

 theorem candidateWeight_inverse_difference {f g : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight 1 f) (hg : CandidateWeight 1 g)
    (hf1 : coeff 1 f=1) (hg1 : coeff 1 g=1)
    (hd : CandidateWeight 2 (f-g)) :
    CandidateWeight 2 (f.substInvOfIsUnit (by rw [hf1]; exact isUnit_one)-
      g.substInvOfIsUnit (by rw [hg1]; exact isUnit_one)) := by
  let fu : IsUnit (coeff 1 f) := by rw [hf1]; exact isUnit_one
  let gu : IsUnit (coeff 1 g) := by rw [hg1]; exact isUnit_one
  let F := f.substInvOfIsUnit fu
  let G := g.substInvOfIsUnit gu
  have hF : CandidateWeight 1 F := hf.substInvOfIsUnit hf1 fu
  have hG : CandidateWeight 1 G := hg.substInvOfIsUnit hg1 gu
  have hf0 := hf.constantCoeff_eq_zero (by omega)
  have hg0 := hg.constantCoeff_eq_zero (by omega)
  have hGs := HasSubst.of_constantCoeff_zero' (hG.constantCoeff_eq_zero (by omega))
  have hfg : CandidateWeight 2 (f.subst G-X) := by
    have h := hd.subst hG
    rw [← coe_substAlgHom hGs,map_sub,coe_substAlgHom,
      subst_substInvOfIsUnit_right g hg0 gu] at h
    exact h
  have hh := candidateWeight_subst_difference hF (hf.subst hG) candidateWeight_X hfg
  rw [← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hf0) hGs,
    subst_substInvOfIsUnit_left f hf0 fu,subst_X hGs,X_subst] at hh
  simpa only [neg_sub] using hh.neg

end Dowling
