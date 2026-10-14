import BoseBurton.KernelReindexExpanded
import BoseBurton.RankZRows

noncomputable section
namespace BoseBurton
open Finset Polynomial

theorem correctionRow_reindex (q : ℝ) (r s : ℕ) (hsr : s≤r) :
    projectiveRow q r+
      (∑ d∈Icc 1 r,C ((-1:ℝ)^d)*correctionRow q r s d*projectiveRow q (r-d))=
      originalSignedKernel q r s := by
  rw [originalSignedKernel]
  congr 1
  rw [← kernel_reindex_expanded q r s hsr]
  apply sum_congr rfl
  intro d _
  rw [correctionRow,mul_sum,sum_mul]
  apply sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial]
  simp only [map_mul]
  ring

end BoseBurton
