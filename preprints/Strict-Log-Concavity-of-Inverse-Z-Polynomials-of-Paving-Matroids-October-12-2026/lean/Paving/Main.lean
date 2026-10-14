import Paving.HigherRankMain
import Paving.LowRankMain

namespace Paving
open MatroidInverseZ
variable {α : Type*} [Fintype α]

/-- Every supported coefficient is positive for every positive-rank paving matroid. -/
theorem IsPaving.coefficient_pos {M : Matroid α} (hM : IsPaving M)
    (hr : 1≤rank M) (k : ℕ) (hk : k≤rank M) : 0 < (matroidInverseZ M).coeff k := by
  by_cases hlow : rank M≤2
  · exact low_rank_positive hM hr hlow k hk
  · exact hM.coefficient_pos_higher (by omega) k hk

theorem IsPaving.coefficient_strict {M : Matroid α} (hM : IsPaving M)
    (hr : 1≤rank M) (k : ℕ) (hk : 1≤k) (hkr : k<rank M) :
    (matroidInverseZ M).coeff (k-1)*(matroidInverseZ M).coeff (k+1) <
      (matroidInverseZ M).coeff k^2 := by
  by_cases hlow : rank M≤2
  · exact low_rank_strict hM hr hlow k hk hkr
  · exact hM.coefficient_strict_higher (by omega) k hk hkr

/-- The original all-positive-rank theorem: no size, connectedness, coloop,
representability, sparse-paving, or parity restriction is imposed. -/
theorem paving_inverseZ_main (M : Matroid α) [M.Loopless] (hM : IsPaving M)
    (hr : 1≤rank M) :
    (matroidInverseZ M).natDegree=rank M ∧
    (∀ k≤rank M, 0 < (matroidInverseZ M).coeff k) ∧
    (∀ k≤rank M, (matroidInverseZ M).coeff (rank M-k)=(matroidInverseZ M).coeff k) ∧
    (∀ k, 1≤k → k<rank M →
      (matroidInverseZ M).coeff (k-1)*(matroidInverseZ M).coeff (k+1)<
        (matroidInverseZ M).coeff k^2) := by
  refine ⟨?_,fun k hk => hM.coefficient_pos hr k hk,
    fun k hk => (actual_inverseZ_coeff_symm M k hk).symm,
    fun k hk hkr => hM.coefficient_strict hr k hk hkr⟩
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (actual_inverseZ_degree_le M)
    (ne_of_gt (hM.coefficient_pos hr (rank M) le_rfl))

end Paving
