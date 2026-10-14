import Dowling.FullInverseZIdentification
import Dowling.DowlingInverseZCandidatePositivity

noncomputable section
namespace Dowling
variable {G : Type*} [Group G] [Fintype G]

theorem fullY_coeff_pos (n k : ℕ) (hk : k≤n) : 0<(fullY G n).coeff k := by
  have hm : (0:ℝ)<Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  have h := dowlingScalarCoefficient_pos (inv_pos.mpr hm) n k hk
  have hc : (0:ℝ)<((fullY G n).coeff k : ℝ) := by
    rw [fullY_coeff_real]
    exact mul_pos (mul_pos (by positivity) (pow_pos hm n)) h
  exact_mod_cast hc

theorem fullY_coeff_above (n k : ℕ) (hk : n<k) : (fullY G n).coeff k=0 := by
  have hc : ((fullY G n).coeff k : ℝ)=0 := by
    rw [fullY_coeff_real,dowlingScalarCoefficient_above _ n k hk,mul_zero]
  exact_mod_cast hc

theorem fullY_natDegree (n : ℕ) : (fullY G n).natDegree=n := by
  apply le_antisymm
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => fullY_coeff_above n k hk)
  · exact Polynomial.le_natDegree_of_ne_zero (ne_of_gt (fullY_coeff_pos n n le_rfl))

end Dowling
