import Dowling.FullInverseZProperties
import Dowling.DowlingMixtureStrict

noncomputable section
namespace Dowling
variable {G : Type*} [Group G] [Fintype G]

/-- Every internal coefficient of the genuine full-Dowling inverse-Z
polynomial satisfies the strict Turán inequality. -/
theorem fullY_strict_log_concave (n k : ℕ) (hk : 1≤k) (hkn : k<n) :
    (fullY G n).coeff (k-1)*(fullY G n).coeff (k+1)<((fullY G n).coeff k)^2 := by
  have hm : (0:ℝ)<Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  have h := dowlingScalarCoefficient_strict_log_concave (inv_pos.mpr hm) n k hk hkn
  have hc : (0:ℝ)<(n.factorial : ℝ)*(Fintype.card G : ℝ)^n := by positivity
  have ht := mul_lt_mul_of_pos_left h (sq_pos_of_pos hc)
  have he : (((fullY G n).coeff (k-1) : ℝ))*((fullY G n).coeff (k+1) : ℝ)<
      (((fullY G n).coeff k : ℝ))^2 := by
    rw [fullY_coeff_real,fullY_coeff_real,fullY_coeff_real]
    nlinarith only [ht]
  exact_mod_cast he

theorem full_dowling_inverseZ (n : ℕ) :
    (fullY G n).natDegree=n ∧
    (∀ k, k≤n → 0<(fullY G n).coeff k) ∧
    (∀ k, k≤n → (fullY G n).coeff k=(fullY G n).coeff (n-k)) ∧
    (∀ k, 1≤k → k<n →
      (fullY G n).coeff (k-1)*(fullY G n).coeff (k+1)<((fullY G n).coeff k)^2) :=
  ⟨fullY_natDegree n,fullY_coeff_pos n,fullY_coeff_symm n,fullY_strict_log_concave n⟩

end Dowling
