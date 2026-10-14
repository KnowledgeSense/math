import MainTheorems.Chollet.ZMonotonicity

noncomputable section

open Matrix
open scoped ComplexOrder

namespace ResearchMain.Chollet

variable {I : Type*} [Fintype I] [DecidableEq I]

def rankOne (x : I → ℂ) : Matrix I I ℂ := vecMulVec x (star x)

def pencil (B : Matrix I I ℂ) (x : I → ℂ) (η : ℝ) : Matrix I I ℂ :=
  B + η • rankOne x

omit [DecidableEq I] in
theorem rankOne_positiveSemidefinite (x : I → ℂ) : (rankOne x).PosSemidef :=
  posSemidef_vecMulVec_self_star x

omit [DecidableEq I] in
theorem pencil_hermitian {B : Matrix I I ℂ} (hB : B.IsHermitian) (x : I → ℂ) (η : ℝ) :
    (pencil B x η).IsHermitian := by
  apply hB.add
  exact (rankOne_positiveSemidefinite x).isHermitian.smul (by simp [IsSelfAdjoint])

omit [Fintype I] in
theorem pencil_comparison_bound (B : Matrix I I ℂ) (x : I → ℂ) (η : ℝ) (i j : I) :
    comparison B i j - |η| * (‖x i‖ * ‖x j‖) +
      (if i = j then (η + |η|) * ‖x i‖ ^ 2 else 0) ≤ comparison (pencil B x η) i j := by
  by_cases he : i = j
  · subst j
    simp only [comparison, pencil, Matrix.add_apply, Matrix.smul_apply,
      rankOne, vecMulVec_apply, Pi.star_apply]
    have hx : x i * star (x i) = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hx]
    simp only [ite_true, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  · have hn := norm_add_le (B i j) ((η : ℝ) • (x i * star (x j)))
    simp only [norm_smul, Real.norm_eq_abs, norm_mul, norm_star] at hn
    simpa [comparison, he, pencil, rankOne, vecMulVec_apply, mul_assoc, add_comm] using (neg_le_neg hn)

theorem pencil_closure {B : Matrix I I ℂ} (hB : B.IsHermitian) (x : I → ℂ)
    (hS : (comparison B - vecMulVec (fun i => ‖x i‖) (fun i => ‖x i‖)).PosSemidef)
    (η : ℝ) (hη : |η| ≤ 1) : ComparisonPSD (pencil B x η) := by
  let Y : Matrix I I ℝ := vecMulVec (fun i => ‖x i‖) (fun i => ‖x i‖)
  let D : Matrix I I ℝ := diagonal (fun i => (η + |η|) * ‖x i‖ ^ 2)
  let L := comparison B - |η| • Y + D
  have hY : Y.PosSemidef := by simpa [Y] using
    posSemidef_vecMulVec_self_star (fun i => ‖x i‖)
  have hD : D.PosSemidef := by
    apply PosSemidef.diagonal
    intro i
    exact mul_nonneg (by linarith [neg_abs_le η]) (sq_nonneg _)
  have hL : L.PosSemidef := by
    have h := (hS.add (hY.smul (show 0 ≤ 1 - |η| by linarith))).add hD
    convert h using 1
    funext i j
    simp only [L, D, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Y]
    ring
  refine ⟨pencil_hermitian hB x η, ?_⟩
  apply z_matrix_psd_enlargement hL (comparison_hermitian (pencil_hermitian hB x η))
  · intro i j hij
    simp only [comparison, ite_eq_right hij]
    exact neg_nonpos.mpr (norm_nonneg _)
  · intro i j
    simpa only [L, D, Y, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, vecMulVec_apply, diagonal_apply] using pencil_comparison_bound B x η i j

end ResearchMain.Chollet
