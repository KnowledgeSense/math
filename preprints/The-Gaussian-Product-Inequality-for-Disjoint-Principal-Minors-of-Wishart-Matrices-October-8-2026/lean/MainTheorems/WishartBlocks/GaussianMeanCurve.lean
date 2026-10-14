import MainTheorems.WishartBlocks.RegularizedProductJetMoments
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators InnerProductSpace MatrixOrder Matrix.Norms.Elementwise ContDiff

noncomputable def oneRowMatrixFirst {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.vecMulVec (fun i => oneRowGaussianVector S v s x i) (fun i => v i) +
    Matrix.vecMulVec (fun i => v i) (fun i => oneRowGaussianVector S v s x i)

noncomputable def oneRowMatrixSecond {p : ℕ} (v : EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ := (2 : ℝ) • Matrix.vecMulVec (fun i => v i) (fun i => v i)

theorem oneRowWishartValue_hasDerivAt {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) :
    HasDerivAt (fun t : ℝ => oneRowWishartValue S (t • v) x) (oneRowMatrixFirst S v s x) s := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  let a := (CFC.sqrt S).toEuclideanLin x.2
  have hi := (hasDerivAt_const s (a i)).add ((hasDerivAt_id' s).mul_const (v i))
  have hj := (hasDerivAt_const s (a j)).add ((hasDerivAt_id' s).mul_const (v j))
  convert (hasDerivAt_const s (x.1 i j)).add (hi.mul hj) using 1
  · funext t
    simp only [oneRowWishartValue, gaussianMeanGram,
      Matrix.add_apply, Matrix.vecMulVec_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rfl
  · simp only [oneRowMatrixFirst, oneRowGaussianVector, Matrix.add_apply,
      Matrix.vecMulVec_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    dsimp [a]
    ring

theorem oneRowMatrixFirst_hasDerivAt {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) :
    HasDerivAt (fun t : ℝ => oneRowMatrixFirst S v t x) (oneRowMatrixSecond v) s := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  let a := (CFC.sqrt S).toEuclideanLin x.2
  have hi := (hasDerivAt_const s (a i)).add ((hasDerivAt_id' s).mul_const (v i))
  have hj := (hasDerivAt_const s (a j)).add ((hasDerivAt_id' s).mul_const (v j))
  convert (hi.mul_const (v j)).add (hj.const_mul (v i)) using 1
  · funext t
    simp only [oneRowMatrixFirst, oneRowGaussianVector, Matrix.add_apply,
      Matrix.vecMulVec_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rfl
  · simp only [oneRowMatrixSecond, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    ring

theorem oneRowMatrixFirst_norm_bound {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) :
    ‖oneRowMatrixFirst S v s x‖ ≤ 2 * ‖oneRowGaussianVector S v s x‖ * ‖v‖ := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  change ‖oneRowGaussianVector S v s x i * v j + v i * oneRowGaussianVector S v s x j‖ ≤ _
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  have hi := PiLp.norm_apply_le (oneRowGaussianVector S v s x) i
  have hj := PiLp.norm_apply_le (oneRowGaussianVector S v s x) j
  have hvi := PiLp.norm_apply_le v i
  have hvj := PiLp.norm_apply_le v j
  nlinarith [mul_le_mul hi hvj (norm_nonneg _) (norm_nonneg _),
    mul_le_mul hvi hj (norm_nonneg _) (norm_nonneg _)]

theorem oneRowMatrixSecond_norm_bound {p : ℕ} (v : EuclideanSpace ℝ (Fin p)) :
    ‖oneRowMatrixSecond v‖ ≤ 2 * ‖v‖ ^ 2 := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  simp only [oneRowMatrixSecond, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, norm_mul]
  norm_num
  have hb : |v i| * |v j| ≤ ‖v‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, pow_two] using
      mul_le_mul (PiLp.norm_apply_le v i) (PiLp.norm_apply_le v j)
        (norm_nonneg (v j)) (norm_nonneg v)
  nlinarith [hb]

noncomputable def gaussianMatrixTest {p : ℕ} (f : MatrixEuclidean p → ℂ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p))
    (s : ℝ) (x : OneRowInput p) : ℂ :=
  f (matrixCoordinates p (oneRowWishartValue S (s • v) x))

noncomputable def gaussianMatrixTestFirst {p : ℕ} (f : MatrixEuclidean p → ℂ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p))
    (s : ℝ) (x : OneRowInput p) : ℂ :=
  fderiv ℝ f (matrixCoordinates p (oneRowWishartValue S (s • v) x))
    (matrixCoordinates p (oneRowMatrixFirst S v s x))

noncomputable def gaussianMatrixTestSecond {p : ℕ} (f : MatrixEuclidean p → ℂ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p))
    (s : ℝ) (x : OneRowInput p) : ℂ :=
  fderiv ℝ (fderiv ℝ f) (matrixCoordinates p (oneRowWishartValue S (s • v) x))
      (matrixCoordinates p (oneRowMatrixFirst S v s x))
        (matrixCoordinates p (oneRowMatrixFirst S v s x)) +
    fderiv ℝ f (matrixCoordinates p (oneRowWishartValue S (s • v) x))
      (matrixCoordinates p (oneRowMatrixSecond v))

theorem gaussianMatrixTest_hasDerivAt {p : ℕ} {f : MatrixEuclidean p → ℂ}
    (hf : ContDiff ℝ ∞ f) (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) :
    HasDerivAt (fun t => gaussianMatrixTest f S v t x) (gaussianMatrixTestFirst f S v s x) s := by
  have hW := (matrixCoordinates p).hasFDerivAt.comp_hasDerivAt s
    (oneRowWishartValue_hasDerivAt S v s x)
  exact ((hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt s hW)

theorem gaussianMatrixTestFirst_hasDerivAt {p : ℕ} {f : MatrixEuclidean p → ℂ}
    (hf : ContDiff ℝ ∞ f) (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) :
    HasDerivAt (fun t => gaussianMatrixTestFirst f S v t x)
      (gaussianMatrixTestSecond f S v s x) s := by
  have hW := (matrixCoordinates p).hasFDerivAt.comp_hasDerivAt s
    (oneRowWishartValue_hasDerivAt S v s x)
  have hH := (matrixCoordinates p).hasFDerivAt.comp_hasDerivAt s
    (oneRowMatrixFirst_hasDerivAt S v s x)
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdf := ((hfd.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt s hW
  exact hdf.clm_apply hH

theorem gaussianMatrixTestFirst_jet_bound {p : ℕ} (f : MatrixEuclidean p → ℂ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) :
    ‖gaussianMatrixTestFirst f S v s x‖ ≤
      ‖iteratedFDeriv ℝ 1 f (matrixCoordinates p (oneRowWishartValue S (s • v) x))‖ *
        ‖matrixCoordinates p (oneRowMatrixFirst S v s x)‖ := by
  rw [norm_iteratedFDeriv_one]
  exact (fderiv ℝ f _).le_opNorm _

theorem gaussianMatrixTestSecond_jet_bound {p : ℕ} (f : MatrixEuclidean p → ℂ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) :
    ‖gaussianMatrixTestSecond f S v s x‖ ≤
      ‖iteratedFDeriv ℝ 2 f (matrixCoordinates p (oneRowWishartValue S (s • v) x))‖ *
        ‖matrixCoordinates p (oneRowMatrixFirst S v s x)‖ ^ 2 +
      ‖iteratedFDeriv ℝ 1 f (matrixCoordinates p (oneRowWishartValue S (s • v) x))‖ *
        ‖matrixCoordinates p (oneRowMatrixSecond v)‖ := by
  unfold gaussianMatrixTestSecond
  apply (norm_add_le _ _).trans
  rw [norm_iteratedFDeriv_one, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
  apply add_le_add _ ((fderiv ℝ f _).le_opNorm _)
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) _ _‖ * ‖matrixCoordinates p (oneRowMatrixFirst S v s x)‖ :=
      (fderiv ℝ (fderiv ℝ f) _ _).le_opNorm _
    _ ≤ (‖fderiv ℝ (fderiv ℝ f) _‖ * ‖matrixCoordinates p (oneRowMatrixFirst S v s x)‖) *
        ‖matrixCoordinates p (oneRowMatrixFirst S v s x)‖ :=
      mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ f) _).le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

end ResearchMain.WishartBlocks
