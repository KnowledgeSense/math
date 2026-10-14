import Dowling.DowlingCandidateDefinitions

noncomputable section
namespace Dowling
open PowerSeries Finset

/-- Every monomial has outer degree at least twice its parameter degree plus `w`. -/
def CandidateWeight (w : ℕ) (f : PowerSeries (Polynomial ℝ)) : Prop :=
  ∀ n k, n < 2*k+w → (coeff n f).coeff k = 0

theorem candidateWeight_zero (w : ℕ) : CandidateWeight w 0 := by
  intro n k _
  simp

theorem CandidateWeight.mono {w v : ℕ} {f : PowerSeries (Polynomial ℝ)}
    (h : CandidateWeight w f) (hv : v ≤ w) : CandidateWeight v f := by
  intro n k hn
  exact h n k (by omega)

theorem CandidateWeight.add {w : ℕ} {f g : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight w f) (hg : CandidateWeight w g) : CandidateWeight w (f+g) := by
  intro n k hn
  simp only [map_add, Polynomial.coeff_add, hf n k hn, hg n k hn, add_zero]

theorem CandidateWeight.neg {w : ℕ} {f : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight w f) : CandidateWeight w (-f) := by
  intro n k hn
  simp only [map_neg, Polynomial.coeff_neg, hf n k hn, neg_zero]

theorem CandidateWeight.sub {w : ℕ} {f g : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight w f) (hg : CandidateWeight w g) : CandidateWeight w (f-g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem CandidateWeight.mul {v w : ℕ} {f g : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight v f) (hg : CandidateWeight w g) :
    CandidateWeight (v+w) (f*g) := by
  intro n k hn
  rw [coeff_mul, Polynomial.finsetSum_coeff]
  apply sum_eq_zero
  intro ij hij
  rw [Polynomial.coeff_mul]
  apply sum_eq_zero
  intro ab hab
  have hij' := mem_antidiagonal.mp hij
  have hab' := mem_antidiagonal.mp hab
  by_cases h : ij.1 < 2*ab.1+v
  · rw [hf _ _ h, zero_mul]
  · rw [hg _ _ (by omega), mul_zero]

theorem candidateWeight_one : CandidateWeight 0 1 := by
  intro n k hn
  by_cases hn0 : n=0
  · subst n
    have hk : k≠0 := by omega
    simp [Polynomial.coeff_one, hk]
  · simp [coeff_one, hn0]

theorem CandidateWeight.pow {w : ℕ} {f : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight w f) (r : ℕ) : CandidateWeight (r*w) (f^r) := by
  induction r with
  | zero => simpa using candidateWeight_one
  | succ r ih =>
    simpa only [pow_succ, Nat.succ_mul] using ih.mul hf

theorem CandidateWeight.constantCoeff_eq_zero {w : ℕ} {f : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight w f) (hw : 0<w) : f.constantCoeff=0 := by
  apply Polynomial.ext
  intro k
  rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_zero]
  exact hf 0 k (by omega)

/-- Zero-constant substitution has a finite coefficient expansion. -/
theorem candidate_coeff_subst (f g : PowerSeries (Polynomial ℝ))
    (hg : g.constantCoeff = 0) (n : ℕ) :
    coeff n (f.subst g) = ∑ d ∈ range (n+1), coeff d f * coeff n (g^d) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  change coeff d f * coeff n (g^d) ≠ 0 at hd
  by_contra hdn
  have hgt : ¬d ≤ n := by simpa only [mem_coe, mem_range, Nat.lt_succ_iff] using hdn
  obtain ⟨q,rfl⟩ := X_dvd_iff.mpr hg
  apply hd
  rw [mul_pow, coeff_X_pow_mul', ite_eq_right hgt, mul_zero]

theorem CandidateWeight.subst {w : ℕ} {f g : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight w f) (hg : CandidateWeight 1 g) :
    CandidateWeight w (f.subst g) := by
  intro n k hn
  rw [candidate_coeff_subst f g (hg.constantCoeff_eq_zero (by omega)),
    Polynomial.finsetSum_coeff]
  apply sum_eq_zero
  intro d _
  rw [Polynomial.coeff_mul]
  apply sum_eq_zero
  intro ab hab
  have hab' := mem_antidiagonal.mp hab
  by_cases h : d < 2*ab.1+w
  · rw [hf _ _ h, zero_mul]
  · have hp := hg.pow d
    rw [hp n ab.2 (by omega), mul_zero]

end Dowling
