import Paving.HighCoefficients

namespace Paving
open MatroidInverseZ Polynomial Finset
variable {α : Type*} [Fintype α]

/-- No reflected scalar row is used beyond the actual matroid rank. -/
theorem actual_inverseZ_high_coeff (M : Matroid α) (k : ℕ) (hk : rank M<k) :
    (matroidInverseZ M).coeff k = 0 := by
  classical
  rw [actual_inverseZ_sum,finsetSum_coeff]
  apply sum_eq_zero
  intro F _
  rw [flatSummand,mul_assoc,coeff_C_mul,coeff_X_pow_mul',ite_eq_left (by omega)]
  have hf : MatroidInverseZ.flatRank M F≤rank M := subsetRank_le M F.1
  by_cases he : F=⊥
  · subst F
    rw [inverseKL_self,actualFlatRank_bot,Nat.sub_zero,coeff_one,ite_eq_right (by omega),mul_zero]
  · rw [inverseKL_high_coeff (MatroidInverseZ.flatRank M) (actualFlatRank_strictMono M).monotone
      ⊥ F bot_le (Ne.symm he) _ (by simp only [actualFlatRank_bot,Nat.sub_zero]; omega),mul_zero]

theorem actual_inverseZ_degree_le (M : Matroid α) : (matroidInverseZ M).natDegree≤rank M :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (actual_inverseZ_high_coeff M)

end Paving
