import MainTheorems.Chollet.Comparison

open Matrix

namespace ResearchMain.Chollet

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
theorem z_matrix_term_bound (N : Matrix I I ℝ)
    (hN : ∀ i j, i ≠ j → N i j ≤ 0) (v : I → ℝ) (i j : I) :
    |v i| * N i j * |v j| ≤ v i * N i j * v j := by
  by_cases he : i = j
  · subst j
    apply le_of_eq
    calc
      |v i| * N i i * |v i| = N i i * |v i| ^ 2 := by ring
      _ = N i i * v i ^ 2 := by rw [sq_abs]
      _ = v i * N i i * v i := by ring
  · have ha : v i * v j ≤ |v i| * |v j| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h := mul_le_mul_of_nonpos_left ha (hN i j he)
    nlinarith

theorem z_matrix_psd_enlargement {M N : Matrix I I ℝ} (hM : M.PosSemidef)
    (hNh : N.IsHermitian) (hNz : ∀ i j, i ≠ j → N i j ≤ 0)
    (hMN : ∀ i j, M i j ≤ N i j) : N.PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg hNh
  intro v
  have hm := hM.dotProduct_mulVec_nonneg (fun i => |v i|)
  apply hm.trans
  simp only [dotProduct, mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    |v i| * (M i j * |v j|) ≤ |v i| * (N i j * |v j|) := by
      gcongr
      exact hMN i j
    _ ≤ v i * (N i j * v j) := by
      simpa only [mul_assoc] using z_matrix_term_bound N hNz v i j

end ResearchMain.Chollet
