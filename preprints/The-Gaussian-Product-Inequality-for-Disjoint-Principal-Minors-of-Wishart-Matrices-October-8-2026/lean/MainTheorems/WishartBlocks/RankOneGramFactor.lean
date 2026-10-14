import MainTheorems.WishartBlocks.MeanRowRotations
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators MatrixOrder InnerProductSpace

theorem orthonormalBasis_containing_unit (n : ℕ)
    (a : EuclideanSpace ℝ (Fin (n + 1))) (ha : ‖a‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin (n + 1))), b 0 = a := by
  classical
  let v : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) := fun _ => a
  have hv : Orthonormal ℝ (({0} : Set (Fin (n + 1))).domRestrict v) := by
    constructor
    · intro i
      exact ha
    · intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = Fintype.card (Fin (n + 1))) hv
  exact ⟨b, hb 0 (by simp)⟩

theorem orthonormal_images_gram {p k : ℕ}
    (b : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)))
    (R : Matrix (Fin p) (Fin k) ℝ) :
    meanRowGram (fun i => (R.toLpLin 2 2) (b i)) = R * R.transpose := by
  have he (i : Fin k) (j : Fin p) :
      (R.toLpLin 2 2) (b i) j = ⟪WithLp.toLp 2 (R j), b i⟫_ℝ := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]
  ext i j
  simp only [meanRowGram, Matrix.sum_apply, Matrix.vecMulVec_apply, he]
  rw [show (∑ l, ⟪WithLp.toLp 2 (R i), b l⟫_ℝ *
        ⟪WithLp.toLp 2 (R j), b l⟫_ℝ) =
      ⟪WithLp.toLp 2 (R i), WithLp.toLp 2 (R j)⟫_ℝ by
    simpa only [real_inner_comm] using
      b.sum_inner_mul_inner (WithLp.toLp 2 (R i)) (WithLp.toLp 2 (R j))]
  simp [PiLp.inner_apply, Matrix.mul_apply, Matrix.transpose_apply, mul_comm]

theorem rankOne_gram_factor {p n : ℕ} {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hW : W.PosDef) (K : Matrix (Fin (n + 1)) (Fin p) ℝ)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : u ≠ 0) :
    ∃ (θ : ℝ) (M : Fin n → EuclideanSpace ℝ (Fin p)), 0 < θ ∧
      meanRowGram (Fin.cons (Real.sqrt θ • (K.transpose.toLpLin 2 2) u) M) =
        K.transpose * W * K := by
  let R := CFC.sqrt W
  let a := (R⁻¹).toEuclideanLin u
  have hR : IsUnit R.det := positive_sqrt_isUnit_det hW
  have hRa : R.toEuclideanLin a = u := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      Matrix.mul_nonsing_inv _ hR, Matrix.toLpLin_one, LinearMap.id_apply]
  have ha : a ≠ 0 := by
    intro h
    apply hu
    rw [← hRa, h, map_zero]
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hunit : ‖‖a‖⁻¹ • a‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖a‖⁻¹),
      inv_mul_cancel₀ hna.ne']
  obtain ⟨b, hb⟩ := orthonormalBasis_containing_unit n (‖a‖⁻¹ • a) hunit
  let T := K.transpose * R
  let M : Fin n → EuclideanSpace ℝ (Fin p) := fun i => (T.toLpLin 2 2) (b i.succ)
  let θ := (‖a‖⁻¹) ^ 2
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hsqrt : Real.sqrt θ = ‖a‖⁻¹ := by
    dsimp [θ]
    rw [Real.sqrt_sq (by positivity : 0 ≤ ‖a‖⁻¹)]
  have hfirst : (T.toLpLin 2 2) (b 0) =
      Real.sqrt θ • (K.transpose.toLpLin 2 2) u := by
    rw [hb, map_smul, hsqrt]
    congr 1
    rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    rw [hRa]
  have hrows : Fin.cons (Real.sqrt θ • (K.transpose.toLpLin 2 2) u) M =
      fun i => (T.toLpLin 2 2) (b i) := by
    funext i
    refine Fin.cases (by simpa only [Fin.cons_zero] using hfirst.symm)
      (fun j => by simp only [Fin.cons_succ, M]) i
  refine ⟨θ, M, hθ, ?_⟩
  rw [hrows, orthonormal_images_gram]
  have hRt : R.transpose = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg W).posSemidef.1.eq
  have hRR : R * R = W := CFC.sqrt_mul_sqrt_self W hW.posSemidef.nonneg
  dsimp [T]
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, hRt]
  simpa only [Matrix.mul_assoc] using congrArg (fun X => K.transpose * X * K) hRR

theorem congruence_rankOne_gram {p k : ℕ} (K : Matrix (Fin k) (Fin p) ℝ)
    (u : EuclideanSpace ℝ (Fin k)) :
    K.transpose * Matrix.vecMulVec (fun i => u i) (fun i => u i) * K =
      Matrix.vecMulVec (fun i => (K.transpose.toLpLin 2 2) u i)
        (fun i => (K.transpose.toLpLin 2 2) u i) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose]
  rfl

theorem rankOne_gram_increment {p k : ℕ} (K : Matrix (Fin k) (Fin p) ℝ)
    (W : Matrix (Fin k) (Fin k) ℝ) (u : EuclideanSpace ℝ (Fin k)) (c : ℝ) :
    K.transpose * (W + c • Matrix.vecMulVec (fun i => u i) (fun i => u i)) * K =
      K.transpose * W * K + c • Matrix.vecMulVec
        (fun i => (K.transpose.toLpLin 2 2) u i) (fun i => (K.transpose.toLpLin 2 2) u i) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    congruence_rankOne_gram]

end ResearchMain.WishartBlocks
