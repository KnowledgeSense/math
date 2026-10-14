import MainTheorems.WishartBlocks.SpectralLaw.CholeskyExistence
import MainTheorems.WishartBlocks.SpectralLaw.HaarPolynomialGrowth
import MainTheorems.WishartBlocks.RegularizedMatrices

namespace ResearchMain.WishartBlocks

open MeasureTheory
open scoped MatrixOrder Matrix.Norms.Elementwise

theorem continuous_matrixCongruence {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (matrixCongruence L) := by
  unfold matrixCongruence
  fun_prop

theorem choleskyFactor_isUnit {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : IsUnit (choleskyFactor hA) := by
  have hdet : (choleskyFactor hA).det * (choleskyFactor hA).det = A.det := by
    simpa only [Matrix.det_mul, Matrix.det_transpose] using
      congrArg Matrix.det (choleskyFactor_gram hA)
  exact (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr fun h => hA.det_pos.ne' (by simpa only [h, zero_mul] using hdet.symm))

theorem choleskyCongruence_posDef {n : ℕ} {A W : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hW : W.PosDef) :
    (matrixCongruence (choleskyFactor hA) W).PosDef := by
  simpa only [matrixCongruence, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hW.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit (choleskyFactor_isUnit hA))

theorem matrixCongruence_monotone {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) :
    Monotone (matrixCongruence L) := by
  intro W V hWV
  change (V - W).PosSemidef at hWV
  change (matrixCongruence L V - matrixCongruence L W).PosSemidef
  have h := hWV.mul_mul_conjTranspose_same L
  simpa only [matrixCongruence, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem continuousOn_choleskyCongruence_response {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : ContinuousOn G {W | W.PosDef}) :
    ContinuousOn (fun W => G (matrixCongruence (choleskyFactor hA) W)) {W | W.PosDef} :=
  hG.comp (continuous_matrixCongruence _).continuousOn
    (fun _ hW => choleskyCongruence_posDef hA hW)

theorem monotoneOn_choleskyCongruence_response {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : MonotoneOn G {W | W.PosDef}) :
    MonotoneOn (fun W => G (matrixCongruence (choleskyFactor hA) W)) {W | W.PosDef} := by
  intro W hW V hV hWV
  exact hG (choleskyCongruence_posDef hA hW) (choleskyCongruence_posDef hA hV)
    (matrixCongruence_monotone _ hWV)

theorem matrixCongruence_norm_bound {n : ℕ} (L W : Matrix (Fin n) (Fin n) ℝ) :
    ‖matrixCongruence L W‖ ≤ ((n : ℝ) * ‖L‖) ^ 2 * ‖W‖ := by
  calc
    _ ≤ (n : ℝ) * ‖L * W‖ * ‖L.transpose‖ := matrix_product_norm_bound _ _
    _ ≤ (n : ℝ) * ((n : ℝ) * ‖L‖ * ‖W‖) * ‖L.transpose‖ := by
      gcongr
      exact matrix_product_norm_bound L W
    _ = _ := by rw [Matrix.norm_transpose]; ring

theorem choleskyCongruence_response_growth {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} {C β : ℝ} (hC : 0 ≤ C)
    (hb : ∀ W, W.PosDef → ‖G W‖ ≤ C * (1 + ‖W‖) ^ β) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ γ : ℝ, ∀ W, W.PosDef →
      ‖G (matrixCongruence (choleskyFactor hA) W)‖ ≤ D * (1 + ‖W‖) ^ γ := by
  let k := ⌈β⌉₊
  let b := ((n : ℝ) * ‖choleskyFactor hA‖) ^ 2
  have hb0 : 0 ≤ b := sq_nonneg _
  refine ⟨C * (1 + b) ^ k, mul_nonneg hC (by positivity), (k : ℝ), ?_⟩
  intro W hW
  have hn : 1 + ‖matrixCongruence (choleskyFactor hA) W‖ ≤
      (1 + b) * (1 + ‖W‖) := by
    have h := matrixCongruence_norm_bound (choleskyFactor hA) W
    dsimp [b] at ⊢ hb0
    nlinarith [norm_nonneg W]
  calc
    _ ≤ C * (1 + ‖matrixCongruence (choleskyFactor hA) W‖) ^ β :=
      hb _ (choleskyCongruence_posDef hA hW)
    _ ≤ C * (1 + ‖matrixCongruence (choleskyFactor hA) W‖) ^ k := by
      rw [← Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le
          (by linarith [norm_nonneg (matrixCongruence (choleskyFactor hA) W)])
          (Nat.le_ceil β)) hC
    _ ≤ C * ((1 + b) * (1 + ‖W‖)) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn k) hC
    _ = _ := by simp only [Real.rpow_natCast, mul_pow]; ring

theorem choleskyCongruence_det {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (W : Matrix (Fin n) (Fin n) ℝ) :
    (matrixCongruence (choleskyFactor hA) W).det = A.det * W.det := by
  have hd : (choleskyFactor hA).det * (choleskyFactor hA).det = A.det := by
    simpa only [Matrix.det_mul, Matrix.det_transpose] using
      congrArg Matrix.det (choleskyFactor_gram hA)
  simp only [matrixCongruence, Matrix.det_mul, Matrix.det_transpose]
  rw [← hd]
  ring

theorem bartlettLaw_choleskyCongruence {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    (bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ)).map
      (matrixCongruence (choleskyFactor hA)) = bartlettLaw α A := by
  have h := bartlettLaw_covariance_congruence hα hα Matrix.PosSemidef.one (choleskyFactor hA)
  simpa only [matrixCongruence, Matrix.mul_one, choleskyFactor_gram] using h

theorem bartlett_integral_choleskyCongruence {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : Measurable G) :
    (∫ W, G W ∂bartlettLaw α A) =
      ∫ W, G (matrixCongruence (choleskyFactor hA) W) ∂bartlettLaw α 1 := by
  rw [← bartlettLaw_choleskyCongruence hα hA,
    integral_map (measurable_matrixCongruence _).aemeasurable hG.aestronglyMeasurable]

theorem bartlett_weighted_integral_choleskyCongruence {n : ℕ} {α ν : ℝ}
    (hα : (n : ℝ) - 1 < α) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : Measurable G) :
    (∫ W, W.det ^ ν * G W ∂bartlettLaw α A) =
      A.det ^ ν * ∫ W, W.det ^ ν * G (matrixCongruence (choleskyFactor hA) W)
        ∂bartlettLaw α 1 := by
  rw [bartlett_integral_choleskyCongruence hα hA (by fun_prop)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [bartlettLaw_positiveDefinite hα Matrix.PosDef.one] with W hW
  rw [choleskyCongruence_det, Real.mul_rpow hA.det_pos.le hW.det_pos.le]
  ring

end ResearchMain.WishartBlocks
