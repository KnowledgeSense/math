import MainTheorems.WishartBlocks.RegularizedProductBounds
import MainTheorems.WishartBlocks.MatrixEuclidean
import MainTheorems.WishartBlocks.MatrixGaussianLaplace
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ResearchMain.WishartBlocks

open Matrix Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise ContDiff

noncomputable def smoothPositiveFloor (a t : ℝ) : ℝ :=
  a / 2 + Real.smoothTransition ((t - a / 2) / (a / 2)) * (t - a / 2)

theorem smoothPositiveFloor_lower {a : ℝ} (ha : 0 < a) (t : ℝ) :
    a / 2 ≤ smoothPositiveFloor a t := by
  unfold smoothPositiveFloor
  by_cases ht : t ≤ a / 2
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr ht) (by positivity)), zero_mul, add_zero]
  · exact le_add_of_nonneg_right (mul_nonneg (Real.smoothTransition.nonneg _)
      (sub_nonneg.mpr (le_of_not_ge ht)))

theorem smoothPositiveFloor_pos {a : ℝ} (ha : 0 < a) (t : ℝ) :
    0 < smoothPositiveFloor a t := (half_pos ha).trans_le (smoothPositiveFloor_lower ha t)

theorem smoothPositiveFloor_eq {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : a ≤ t) :
    smoothPositiveFloor a t = t := by
  unfold smoothPositiveFloor
  rw [Real.smoothTransition.one_of_one_le ((one_le_div (half_pos ha)).mpr (by linarith))]
  ring

theorem smoothPositiveFloor_contDiff {a : ℝ} (_ha : 0 < a) :
    ContDiff ℝ ∞ (smoothPositiveFloor a) := by
  unfold smoothPositiveFloor
  exact contDiff_const.add
    ((Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const (a / 2))).mul
        (contDiff_id.sub contDiff_const))

theorem smoothPositiveFloor_eventually_eq {a t : ℝ} (ha : 0 < a) (ht : a < t) :
    smoothPositiveFloor a =ᶠ[𝓝 t] id := by
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact smoothPositiveFloor_eq ha hs.le

theorem regularized_determinant_lower {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) {ε : ℝ} (hε : 0 < ε) : ε ^ n ≤ (A + ε • 1).det := by
  have he : A + ε • 1 = ε • (1 + (1 / ε) • A) := by
    simp only [smul_add, smul_smul, mul_one_div_cancel hε.ne', one_smul]
    exact add_comm _ _
  rw [he, Matrix.det_smul, Fintype.card_fin, matrix_one_add_smul_det hA.1]
  have hp : 1 ≤ ∏ i : Fin n, (1 + (1 / ε) * hA.1.eigenvalues i) := by
    simpa only [Finset.prod_const_one] using Finset.prod_le_prod₀
      (s := Finset.univ) (f := fun _ : Fin n => (1 : ℝ))
      (g := fun i => 1 + (1 / ε) * hA.1.eigenvalues i)
      (fun _ _ => zero_le_one) (fun i _ => by
        have hi := mul_nonneg (one_div_nonneg.mpr hε.le) (hA.eigenvalues_nonneg i)
        linarith)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (pow_nonneg hε.le n)

theorem symmetricMatrixPart_eq_of_hermitian {p : ℕ}
    {A : Matrix (Fin p) (Fin p) ℝ} (hA : A.IsHermitian) : symmetricMatrixPart A = A := by
  unfold symmetricMatrixPart
  rw [hA.isSymm]
  module

theorem contDiff_matrix_determinant (n : ℕ) :
    ContDiff ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℝ => A.det) := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  apply ContDiff.sum
  intro σ _
  apply ContDiff.mul contDiff_const
  apply contDiff_prod
  intro i _
  fun_prop

namespace BlockPartition

noncomputable def smoothRegularizedProduct {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε : ℝ) (W : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ∏ j, smoothPositiveFloor (ε ^ P.size j / 2)
    (P.regularizedBlocks ε (symmetricMatrixPart W) j).det ^ ν j

theorem smoothRegularizedProduct_contDiff {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (P.smoothRegularizedProduct ν ε) := by
  unfold smoothRegularizedProduct
  apply contDiff_prod
  intro j _
  have ha : 0 < ε ^ P.size j / 2 := by positivity
  have hM : ContDiff ℝ ∞ (fun W : Matrix (Fin p) (Fin p) ℝ =>
      P.regularizedBlocks ε (symmetricMatrixPart W) j) := by
    dsimp [regularizedBlocks, block, symmetricMatrixPart]
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro k
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.transpose_apply, smul_eq_mul]
    fun_prop
  have hD := (contDiff_matrix_determinant (P.size j)).comp hM
  exact ((smoothPositiveFloor_contDiff ha).comp hD).rpow_const_of_ne
    (fun W => (smoothPositiveFloor_pos ha _).ne')

theorem smoothRegularizedProduct_eq {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) :
    P.smoothRegularizedProduct ν ε W =
      ∏ j, (P.regularizedBlocks ε W j).det ^ ν j := by
  unfold smoothRegularizedProduct
  rw [symmetricMatrixPart_eq_of_hermitian hW.1]
  apply Finset.prod_congr rfl
  intro j _
  rw [smoothPositiveFloor_eq (by positivity)]
  exact (half_le_self (pow_nonneg hε.le (P.size j))).trans
    (regularized_determinant_lower (hW.submatrix (P.inclusion j)) hε)

theorem smoothRegularizedProduct_eventually_eq {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) :
    P.smoothRegularizedProduct ν ε =ᶠ[𝓝 W]
      fun A => ∏ j, (P.regularizedBlocks ε (symmetricMatrixPart A) j).det ^ ν j := by
  have hD (j : Fin d) : ε ^ P.size j / 2 < (P.regularizedBlocks ε W j).det := by
    exact (half_lt_self (by positivity : 0 < ε ^ P.size j)).trans_le
      (regularized_determinant_lower (hW.submatrix (P.inclusion j)) hε)
  have hAll : ∀ j : Fin d, ∀ᶠ A in 𝓝 W,
      ε ^ P.size j / 2 < (P.regularizedBlocks ε (symmetricMatrixPart A) j).det := by
    intro j
    have hc : Continuous (fun A : Matrix (Fin p) (Fin p) ℝ =>
        (P.regularizedBlocks ε (symmetricMatrixPart A) j).det) := by
      dsimp [regularizedBlocks, block, symmetricMatrixPart]
      fun_prop
    have hD' : ε ^ P.size j / 2 <
        (P.regularizedBlocks ε (symmetricMatrixPart W) j).det := by
      simpa only [symmetricMatrixPart_eq_of_hermitian hW.1] using hD j
    exact hc.continuousAt.eventually (eventually_gt_nhds hD')
  filter_upwards [Filter.eventually_all.mpr hAll] with A hA
  unfold smoothRegularizedProduct
  apply Finset.prod_congr rfl
  intro j _
  rw [smoothPositiveFloor_eq (by positivity) (hA j).le]

end BlockPartition
end ResearchMain.WishartBlocks
