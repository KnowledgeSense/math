import Dowling.DowlingCandidateInverseSupport

noncomputable section
namespace Dowling
open PowerSeries Finset

 theorem candidateWeight_realSeries {w : ℕ} (f : PowerSeries ℝ)
    (hf : ∀ n, n<w → coeff n f=0) :
    CandidateWeight w (PowerSeries.map Polynomial.C f) := by
  intro n k hn
  rw [coeff_map, Polynomial.coeff_C]
  split_ifs with hk
  · subst k
    exact hf n (by omega)
  · rfl

theorem CandidateWeight.parameter_mul {w : ℕ} {f : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight (w+2) f) : CandidateWeight w (C Polynomial.X * f) := by
  intro n k hn
  rw [coeff_C_mul]
  cases k with
  | zero => simp
  | succ k =>
    rw [Polynomial.coeff_X_mul]
    exact hf n k (by omega)

theorem candidateWeight_scalar (a : ℝ) :
    CandidateWeight 0 (C (Polynomial.C a)) := by
  intro n k hn
  rw [coeff_C]
  split_ifs with h
  · subst n
    have hk : k≠0 := by omega
    simp [Polynomial.coeff_C,hk]
  · simp

theorem CandidateWeight.scalar_mul {w : ℕ} {f : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight w f) (a : ℝ) : CandidateWeight w (C (Polynomial.C a)*f) := by
  simpa only [zero_add] using (candidateWeight_scalar a).mul hf

 theorem CandidateWeight.exp {f : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight 0 f) (h0 : f.constantCoeff=0) :
    CandidateWeight 0 ((PowerSeries.exp (Polynomial ℝ)).subst f) := by
  intro n k hn
  rw [candidate_coeff_subst _ _ h0, Polynomial.finsetSum_coeff]
  apply sum_eq_zero
  intro d _
  have he : coeff d (PowerSeries.exp (Polynomial ℝ)) =
      Polynomial.C ((d.factorial : ℝ)⁻¹) := by simp [coeff_exp,one_div]
  rw [he,Polynomial.coeff_C_mul]
  have hp := hf.pow d
  rw [hp n k (by omega),mul_zero]

theorem CandidateWeight.exp_sub_one {f : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight 1 f) :
    CandidateWeight 1 ((PowerSeries.exp (Polynomial ℝ)).subst f - 1) := by
  have h0 := hf.constantCoeff_eq_zero (by omega)
  intro n k hn
  by_cases hn0 : n=0
  · subst n
    have hc : ((PowerSeries.exp (Polynomial ℝ)).subst f).constantCoeff=1 := by
      rw [constantCoeff_subst_of_constantCoeff_zero h0]
      exact constantCoeff_exp
    rw [map_sub, coeff_zero_eq_constantCoeff_apply, coeff_one, ite_eq_left rfl]
    rw [← PowerSeries.constantCoeff_eq] at hc
    rw [hc,sub_self]
    simp
  · rw [map_sub, coeff_one, ite_eq_right hn0, sub_zero,
      candidate_coeff_subst _ _ h0, Polynomial.finsetSum_coeff]
    apply sum_eq_zero
    intro d _
    by_cases hd : d=0
    · subst d
      simp [coeff_one,hn0]
    · have he : coeff d (PowerSeries.exp (Polynomial ℝ)) =
          Polynomial.C ((d.factorial : ℝ)⁻¹) := by simp [coeff_exp,one_div]
      rw [he,Polynomial.coeff_C_mul]
      have hp := hf.pow d
      rw [hp n k (by omega),mul_zero]

theorem candidateWeight_realSeries_subst {v w : ℕ} (f : PowerSeries ℝ)
    (hf : ∀ d, d<v → coeff d f=0) {g : PowerSeries (Polynomial ℝ)}
    (hg : CandidateWeight w g) (h0 : g.constantCoeff=0) :
    CandidateWeight (v*w) ((PowerSeries.map Polynomial.C f).subst g) := by
  intro n k hn
  rw [candidate_coeff_subst _ _ h0, Polynomial.finsetSum_coeff]
  apply sum_eq_zero
  intro d _
  rw [coeff_map,Polynomial.coeff_C_mul]
  by_cases hd : d<v
  · rw [hf d hd,zero_mul]
  · have hp := hg.pow d
    rw [hp n k (by have := Nat.mul_le_mul_right w (Nat.le_of_not_gt hd); omega),mul_zero]

end Dowling
