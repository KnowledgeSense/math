import MainTheorems.WishartBlocks.MatrixLaplaceMoments
import MainTheorems.WishartBlocks.RankOneLaplaceDerivatives
import MainTheorems.WishartBlocks.GramContractions

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators InnerProductSpace

theorem trace_outer_factors {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (u v x y : ι → ℝ) :
    (A * Matrix.vecMulVec u v * B * Matrix.vecMulVec x y).trace =
      (v ⬝ᵥ (B *ᵥ x)) * (y ⬝ᵥ (A *ᵥ u)) := by
  rw [Matrix.mul_vecMulVec A u v, Matrix.vecMulVec_mul,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul,
    ← Matrix.dotProduct_mulVec, dotProduct_comm (A *ᵥ u) y]
  rfl

theorem symmetric_mulVec_dotProduct {ι : Type*} [Fintype ι]
    (T : Matrix ι ι ℝ) (hT : T.transpose = T) (v w : ι → ℝ) :
    (T *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (T *ᵥ w) := by
  rw [dotProduct_comm, symmetric_matrix_quadratic_comm T hT v w]

theorem covariance_resolvent_identity {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ)
    (hD : IsUnit (1 + (2 : ℝ) • (S * T)).det) :
    T * (1 + (2 : ℝ) • (S * T))⁻¹ +
      (2 : ℝ) • (T * (1 + (2 : ℝ) • (S * T))⁻¹ * S * T) = T := by
  let P := 1 + (2 : ℝ) • (S * T)
  calc
    _ = T * (P⁻¹ * P) := by
      dsimp only [P]
      simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_assoc]
    _ = T := by rw [Matrix.nonsing_inv_mul P hD, Matrix.mul_one]

theorem covariance_rankOne_trace {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ) (hT : T.transpose = T) (v : Fin p → ℝ) :
    ((1 + (2 : ℝ) • (S * T))⁻¹ *
      ((2 : ℝ) • (S * Matrix.vecMulVec (T *ᵥ v) (T *ᵥ v)))).trace =
      2 * (v ⬝ᵥ ((T * (1 + (2 : ℝ) • (S * T))⁻¹ * S * T) *ᵥ v)) := by
  rw [Matrix.mul_smul, Matrix.trace_smul]
  rw [← Matrix.mul_assoc, trace_matrix_outer, symmetric_mulVec_dotProduct T hT]
  simp only [← Matrix.mulVec_mulVec, Matrix.mul_assoc, smul_eq_mul]

theorem covariance_rankOne_resolvent_trace {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ) (hT : T.transpose = T)
    (hD : IsUnit (1 + (2 : ℝ) • (S * T)).det) (v : Fin p → ℝ) :
    let P := 1 + (2 : ℝ) • (S * T)
    let H := Matrix.vecMulVec (T *ᵥ v) (T *ᵥ v)
    let J := (2 : ℝ) • (S * H)
    let M := Matrix.vecMulVec v v
    (P⁻¹ * (M * H)).trace - (P⁻¹ * J * P⁻¹ * (M * T)).trace =
      (v ⬝ᵥ ((T * P⁻¹) *ᵥ v)) ^ 2 := by
  dsimp only
  let P := 1 + (2 : ℝ) • (S * T)
  let H := Matrix.vecMulVec (T *ᵥ v) (T *ᵥ v)
  let M := Matrix.vecMulVec v v
  let a := v ⬝ᵥ ((T * P⁻¹) *ᵥ v)
  let h := v ⬝ᵥ ((T * P⁻¹ * S * T) *ᵥ v)
  have ha : (T *ᵥ v) ⬝ᵥ (P⁻¹ *ᵥ v) = a := by
    rw [symmetric_mulVec_dotProduct T hT, Matrix.mulVec_mulVec]
  have hf : (P⁻¹ * (M * H)).trace = (v ⬝ᵥ (T *ᵥ v)) * a := by
    change (P⁻¹ * (Matrix.vecMulVec v v *
      Matrix.vecMulVec (T *ᵥ v) (T *ᵥ v))).trace = _
    rw [← Matrix.mul_assoc]
    have he := trace_outer_factors P⁻¹ (1 : Matrix (Fin p) (Fin p) ℝ)
      v v (T *ᵥ v) (T *ᵥ v)
    simpa only [Matrix.mul_one, Matrix.one_mulVec, ha] using he
  have hs : (P⁻¹ * ((2 : ℝ) • (S * H)) * P⁻¹ * (M * T)).trace = 2 * a * h := by
    have he : P⁻¹ * ((2 : ℝ) • (S * H)) * P⁻¹ * (M * T) =
        (2 : ℝ) • ((P⁻¹ * S * H * P⁻¹ * M) * T) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [he, Matrix.trace_smul, Matrix.trace_mul_comm]
    have hr : T * (P⁻¹ * S * H * P⁻¹ * M) =
        (T * P⁻¹ * S) * H * P⁻¹ * M := by noncomm_ring
    rw [hr]
    dsimp only [H, M]
    rw [trace_outer_factors, ha]
    dsimp only [h]
    rw [Matrix.mulVec_mulVec]
    ring
  have hrel : a + 2 * h = v ⬝ᵥ (T *ᵥ v) := by
    have he := congrArg (fun A : Matrix (Fin p) (Fin p) ℝ => v ⬝ᵥ (A *ᵥ v))
      (covariance_resolvent_identity S T hD)
    simpa only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, a, h, P] using he
  rw [hf, hs]
  change _ = a ^ 2
  rw [← hrel]
  ring

theorem meanGram_sqrt_scale {p : ℕ} {θ : ℝ} (hθ : 0 ≤ θ)
    (v : EuclideanSpace ℝ (Fin p)) :
    Matrix.vecMulVec (fun i => (Real.sqrt θ • v) i) (fun i => (Real.sqrt θ • v) i) =
      θ • Matrix.vecMulVec (fun i => v i) (fun i => v i) := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, PiLp.smul_apply, smul_eq_mul]
  have hs := Real.mul_self_sqrt hθ
  calc
    _ = (Real.sqrt θ * Real.sqrt θ) * (v i * v j) := by ring
    _ = _ := by rw [hs]

theorem oneRowLaplaceDirectionalCoefficient_rankOne {p : ℕ} {q θ : ℝ}
    (hθ : 0 ≤ θ) {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosSemidef) (v : EuclideanSpace ℝ (Fin p)) :
    oneRowLaplaceDirectionalCoefficient q S T
      (Matrix.vecMulVec (T *ᵥ fun i => v i) (T *ᵥ fun i => v i)) (Real.sqrt θ • v) =
      -q * ((fun i => v i) ⬝ᵥ
        ((T * (1 + (2 : ℝ) • (S * T))⁻¹ * S * T) *ᵥ fun i => v i)) -
        θ * (rankOneLaplaceRate S T v) ^ 2 := by
  have hTs : T.transpose = T := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hT.1.eq
  have hD : IsUnit (1 + (2 : ℝ) • (S * T)).det :=
    isUnit_iff_ne_zero.mpr (covariance_precision_det_pos hS.posSemidef hT).ne'
  let P := 1 + (2 : ℝ) • (S * T)
  let H := Matrix.vecMulVec (T *ᵥ fun i => v i) (T *ᵥ fun i => v i)
  let J := (2 : ℝ) • (S * H)
  let M := Matrix.vecMulVec (fun i => v i) (fun i => v i)
  have ha : ((fun i => v i) ⬝ᵥ ((T * P⁻¹) *ᵥ fun i => v i)) =
      rankOneLaplaceRate S T v := euclidean_dotProduct_matrix v v (T * P⁻¹)
  have hm : (P⁻¹ *
      (Matrix.vecMulVec (fun i => (Real.sqrt θ • v) i)
        (fun i => (Real.sqrt θ • v) i) * H)).trace -
      (P⁻¹ * J * P⁻¹ *
        (Matrix.vecMulVec (fun i => (Real.sqrt θ • v) i)
          (fun i => (Real.sqrt θ • v) i) * T)).trace =
      θ * (rankOneLaplaceRate S T v) ^ 2 := by
    rw [meanGram_sqrt_scale hθ v]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rw [← mul_sub]
    have h := covariance_rankOne_resolvent_trace S T hTs hD (fun i => v i)
    dsimp only at h
    change θ * ((P⁻¹ * (M * H)).trace - (P⁻¹ * J * P⁻¹ * (M * T)).trace) = _
    rw [h, ha]
  unfold oneRowLaplaceDirectionalCoefficient
  dsimp only
  rw [hm, covariance_rankOne_trace S T hTs]
  ring

end ResearchMain.WishartBlocks
