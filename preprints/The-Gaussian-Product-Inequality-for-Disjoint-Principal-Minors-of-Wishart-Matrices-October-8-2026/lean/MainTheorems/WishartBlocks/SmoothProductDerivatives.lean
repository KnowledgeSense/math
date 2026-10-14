import MainTheorems.WishartBlocks.SmoothRegularizedProduct
import MainTheorems.WishartBlocks.CompactCutoff
import MainTheorems.WishartBlocks.CoordinateOperatorNorm

namespace ResearchMain.WishartBlocks

open Matrix Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise ContDiff

theorem symmetricMatrixPart_add_smul {p : ℕ} (W H : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
    symmetricMatrixPart (W + t • H) = symmetricMatrixPart W + t • symmetricMatrixPart H := by
  ext i j
  simp only [symmetricMatrixPart, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul]
  ring

theorem symmetricMatrixPart_norm_le {p : ℕ} (H : Matrix (Fin p) (Fin p) ℝ) :
    ‖symmetricMatrixPart H‖ ≤ ‖H‖ := by
  unfold symmetricMatrixPart
  rw [norm_smul, Real.norm_eq_abs]
  norm_num
  exact (mul_le_mul_of_nonneg_left (norm_add_le H H.transpose) (by positivity)).trans_eq
    (by rw [Matrix.norm_transpose]; ring)

namespace BlockPartition

def regularizedFloorGap {p d : ℕ} (P : BlockPartition p d) (ε : ℝ)
    (W : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  ∀ j, ε ^ P.size j / 2 < (P.regularizedBlocks ε (symmetricMatrixPart W) j).det

theorem regularizedFloorGap_positive {p d : ℕ} (P : BlockPartition p d)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    P.regularizedFloorGap ε W := by
  intro j
  rw [symmetricMatrixPart_eq_of_hermitian hW.1]
  exact (half_lt_self (by positivity : 0 < ε ^ P.size j)).trans_le
    (regularized_determinant_lower (hW.submatrix (P.inclusion j)) hε)

theorem regularizedFloorGap_eventually {p d : ℕ} (P : BlockPartition p d)
    {W : Matrix (Fin p) (Fin p) ℝ} {ε : ℝ} (hW : P.regularizedFloorGap ε W) :
    ∀ᶠ A in 𝓝 W, P.regularizedFloorGap ε A := by
  apply Filter.eventually_all.mpr
  intro j
  exact ((by
    dsimp [regularizedBlocks, block, symmetricMatrixPart]
    fun_prop : Continuous (fun A : Matrix (Fin p) (Fin p) ℝ =>
      (P.regularizedBlocks ε (symmetricMatrixPart A) j).det)).continuousAt).eventually
        (eventually_gt_nhds (hW j))

theorem smoothRegularizedProduct_eq_of_gap {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : P.regularizedFloorGap ε W) :
    P.smoothRegularizedProduct ν ε W =
      P.shiftedDeterminantProduct (fun _ => ε • 1) ν (symmetricMatrixPart W) := by
  unfold smoothRegularizedProduct shiftedDeterminantProduct
  apply Finset.prod_congr rfl
  intro j _
  rw [smoothPositiveFloor_eq (by positivity) (hW j).le]
  rfl

theorem smoothRegularizedProduct_hasLineDerivAt {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : P.regularizedFloorGap ε W)
    (H : Matrix (Fin p) (Fin p) ℝ) :
    HasLineDerivAt ℝ (P.smoothRegularizedProduct ν ε)
      (P.regularizedProductDirectional ε ν (symmetricMatrixPart H) (symmetricMatrixPart W)) W H := by
  have hd : ∀ j, 0 < (P.regularizedBlocks ε (symmetricMatrixPart W) j).det :=
    fun j => (by positivity : 0 < ε ^ P.size j / 2).trans (hW j)
  have h := determinant_product_directional (P.regularizedBlocks ε (symmetricMatrixPart W))
    (fun j => P.block (symmetricMatrixPart H) j) ν hd
  have hcurve : HasDerivAt (fun t : ℝ =>
      P.shiftedDeterminantProduct (fun _ => ε • 1) ν
        (symmetricMatrixPart W + t • symmetricMatrixPart H))
      (P.regularizedProductDirectional ε ν (symmetricMatrixPart H) (symmetricMatrixPart W)) 0 := by
    convert h using 1
    · funext t
      change determinantProductValue
        (P.regularizedBlocks ε (symmetricMatrixPart W + t • symmetricMatrixPart H)) ν = _
      apply congrArg (fun A => determinantProductValue A ν)
      funext j
      unfold regularizedBlocks block
      simp only [Matrix.submatrix_add, Matrix.submatrix_smul]
      exact add_right_comm _ _ _
    · rfl
  apply hcurve.congr_of_eventuallyEq
  have hc : ContinuousAt (fun t : ℝ => W + t • H) 0 := by fun_prop
  have he : ∀ᶠ t : ℝ in 𝓝 0, P.regularizedFloorGap ε (W + t • H) := by
    exact hc.eventually (by
      simpa only [zero_smul, add_zero] using P.regularizedFloorGap_eventually hW)
  filter_upwards [he] with t ht
  rw [P.smoothRegularizedProduct_eq_of_gap ν hε ht, symmetricMatrixPart_add_smul]

noncomputable def smoothProductEuclidean {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε : ℝ) (x : MatrixEuclidean p) : ℂ :=
  P.smoothRegularizedProduct ν ε (coordinatesMatrix p x)

theorem smoothProductEuclidean_contDiff {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (P.smoothProductEuclidean ν ε) :=
  Complex.ofRealCLM.contDiff.comp
    ((P.smoothRegularizedProduct_contDiff ν hε).comp (coordinatesMatrix p).contDiff)

theorem smoothProductEuclidean_lineDeriv {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) {x : MatrixEuclidean p}
    (hx : P.regularizedFloorGap ε (coordinatesMatrix p x)) (u : MatrixEuclidean p) :
    lineDeriv ℝ (P.smoothProductEuclidean ν ε) x u =
      (P.regularizedProductDirectional ε ν (symmetricMatrixPart (coordinatesMatrix p u))
        (symmetricMatrixPart (coordinatesMatrix p x)) : ℂ) := by
  have hreal : HasDerivAt (fun t : ℝ => P.smoothRegularizedProduct ν ε
      (coordinatesMatrix p x + t • coordinatesMatrix p u))
      (P.regularizedProductDirectional ε ν (symmetricMatrixPart (coordinatesMatrix p u))
        (symmetricMatrixPart (coordinatesMatrix p x))) 0 :=
    P.smoothRegularizedProduct_hasLineDerivAt ν hε hx (coordinatesMatrix p u)
  have h := hreal.ofReal_comp
  have h' : HasLineDerivAt ℝ (P.smoothProductEuclidean ν ε)
      (P.regularizedProductDirectional ε ν (symmetricMatrixPart (coordinatesMatrix p u))
        (symmetricMatrixPart (coordinatesMatrix p x)) : ℂ) x u := by
    simpa only [HasLineDerivAt, smoothProductEuclidean, map_add, map_smul] using h
  exact h'.lineDeriv

theorem smoothProductEuclidean_second_lineDeriv {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) {x : MatrixEuclidean p}
    (hx : P.regularizedFloorGap ε (coordinatesMatrix p x)) (u v : MatrixEuclidean p) :
    lineDeriv ℝ (fun y => lineDeriv ℝ (P.smoothProductEuclidean ν ε) y v) x u =
      (P.regularizedProductHessian ε ν (symmetricMatrixPart (coordinatesMatrix p v))
        (symmetricMatrixPart (coordinatesMatrix p u))
          (symmetricMatrixPart (coordinatesMatrix p x)) : ℂ) := by
  have hd : ∀ j, 0 < (P.regularizedBlocks ε (symmetricMatrixPart (coordinatesMatrix p x)) j).det :=
    fun j => (by positivity : 0 < ε ^ P.size j / 2).trans (hx j)
  have h := determinant_product_hessian_directional
    (P.regularizedBlocks ε (symmetricMatrixPart (coordinatesMatrix p x)))
    (fun j => P.block (symmetricMatrixPart (coordinatesMatrix p v)) j)
    (fun j => P.block (symmetricMatrixPart (coordinatesMatrix p u)) j) ν hd
  have hcurve : HasLineDerivAt ℝ
      (fun y : MatrixEuclidean p => (P.regularizedProductDirectional ε ν
        (symmetricMatrixPart (coordinatesMatrix p v))
          (symmetricMatrixPart (coordinatesMatrix p y)) : ℂ))
      (P.regularizedProductHessian ε ν (symmetricMatrixPart (coordinatesMatrix p v))
        (symmetricMatrixPart (coordinatesMatrix p u))
          (symmetricMatrixPart (coordinatesMatrix p x)) : ℂ) x u := by
    change HasDerivAt
      (fun t : ℝ => (P.regularizedProductDirectional ε ν
        (symmetricMatrixPart (coordinatesMatrix p v))
          (symmetricMatrixPart (coordinatesMatrix p (x + t • u))) : ℂ))
      (P.regularizedProductHessian ε ν (symmetricMatrixPart (coordinatesMatrix p v))
        (symmetricMatrixPart (coordinatesMatrix p u))
          (symmetricMatrixPart (coordinatesMatrix p x)) : ℂ) 0
    convert h.ofReal_comp using 1
    · funext t
      apply congrArg Complex.ofReal
      unfold regularizedProductDirectional
      apply congrArg (fun A => determinantProductDirectional A
        (fun j => P.block (symmetricMatrixPart (coordinatesMatrix p v)) j) ν)
      funext j
      simp only [map_add, map_smul, symmetricMatrixPart_add_smul, regularizedBlocks,
        block, Matrix.submatrix_add, Matrix.submatrix_smul]
      exact add_right_comm _ _ _
    · rfl
  have he : (fun y => lineDeriv ℝ (P.smoothProductEuclidean ν ε) y v) =ᶠ[𝓝 x]
      (fun y => (P.regularizedProductDirectional ε ν
        (symmetricMatrixPart (coordinatesMatrix p v))
          (symmetricMatrixPart (coordinatesMatrix p y)) : ℂ)) := by
    filter_upwards [((coordinatesMatrix p).continuous.continuousAt).eventually
      (P.regularizedFloorGap_eventually hx)] with y hy
    exact P.smoothProductEuclidean_lineDeriv ν hε hy v
  rw [he.lineDeriv_eq]
  exact hcurve.lineDeriv

theorem smoothProductEuclidean_jet_zero {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) :
    ‖iteratedFDeriv ℝ 0 (P.smoothProductEuclidean ν ε) (matrixCoordinates p W)‖ =
      ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν W‖ := by
  rw [norm_iteratedFDeriv_zero]
  simp only [smoothProductEuclidean, coordinatesMatrix_matrixCoordinates,
    P.smoothRegularizedProduct_eq ν hε hW, Complex.norm_real]
  rfl

theorem smoothProductEuclidean_jet_one {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) :
    ‖iteratedFDeriv ℝ 1 (P.smoothProductEuclidean ν ε) (matrixCoordinates p W)‖ ≤
      ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν W‖ *
        P.regularizedFirstConstant ν ε * coordinatesOperatorNorm p := by
  have hC₁ := P.regularizedFirstConstant_nonneg ν hε
  have hC₀ := coordinatesOperatorNorm_nonneg p
  rw [norm_iteratedFDeriv_one]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [← ((P.smoothProductEuclidean_contDiff ν hε).differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
    P.smoothProductEuclidean_lineDeriv ν hε
      (by simpa only [coordinatesMatrix_matrixCoordinates] using P.regularizedFloorGap_positive hW hε),
    coordinatesMatrix_matrixCoordinates, symmetricMatrixPart_eq_of_hermitian hW.1, Complex.norm_real]
  apply (P.regularizedProductDirectional_bound hW hε ν _).trans
  calc
    _ ≤ ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν W‖ *
        P.regularizedFirstConstant ν ε * (coordinatesOperatorNorm p * ‖u‖) := by
      gcongr
      exact (symmetricMatrixPart_norm_le _).trans (coordinatesMatrix_norm_bound u)
    _ = _ := by ring

theorem smoothProductEuclidean_jet_two {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) :
    ‖iteratedFDeriv ℝ 2 (P.smoothProductEuclidean ν ε) (matrixCoordinates p W)‖ ≤
      ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν W‖ *
        (P.regularizedFirstConstant ν ε ^ 2 + P.regularizedSecondConstant ν ε) *
          coordinatesOperatorNorm p ^ 2 := by
  have hC₁ := P.regularizedFirstConstant_nonneg ν hε
  have hC₂ := P.regularizedSecondConstant_nonneg ν ε
  have hC₀ := coordinatesOperatorNorm_nonneg p
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro m
  have hL := functionDirections_iteratedFDeriv (P.smoothProductEuclidean_contDiff ν hε)
    [m 0, m 1] (matrixCoordinates p W)
  have hm : (fun i : Fin 2 => [m 0, m 1].get i) = m := by
    funext i
    fin_cases i <;> rfl
  simp only [List.length_cons, List.length_nil, hm, functionDirections] at hL
  rw [← hL, P.smoothProductEuclidean_second_lineDeriv ν hε
      (by simpa only [coordinatesMatrix_matrixCoordinates] using P.regularizedFloorGap_positive hW hε),
    coordinatesMatrix_matrixCoordinates, symmetricMatrixPart_eq_of_hermitian hW.1, Complex.norm_real]
  apply (P.regularizedProductHessian_bound hW hε ν _ _).trans
  calc
    _ ≤ ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν W‖ *
        (P.regularizedFirstConstant ν ε ^ 2 + P.regularizedSecondConstant ν ε) *
          (coordinatesOperatorNorm p * ‖m 1‖) * (coordinatesOperatorNorm p * ‖m 0‖) := by
      gcongr
      · exact (symmetricMatrixPart_norm_le _).trans (coordinatesMatrix_norm_bound (m 1))
      · exact (symmetricMatrixPart_norm_le _).trans (coordinatesMatrix_norm_bound (m 0))
    _ = _ := by simp only [Fin.prod_univ_two]; ring

end BlockPartition
end ResearchMain.WishartBlocks
