import MainTheorems.WishartBlocks.SmoothProductDerivatives
import MainTheorems.WishartBlocks.WishartDifferentialCoefficients

namespace ResearchMain.WishartBlocks

open MeasureTheory Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.Elementwise

theorem oneRowInput_matrix_growth_integrable {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ)
    {f : Matrix (Fin p) (Fin p) ℝ → ℝ} (hf : Measurable f)
    {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hB : ∀ W, ‖f W‖ ≤ C * (1 + ‖W‖) ^ β) (k : ℕ) :
    Integrable (fun x : OneRowInput p => (1 + ‖x‖) ^ k *
      ‖f (oneRowWishartValue S (s • v) x)‖) (oneRowInputLaw q S) := by
  let B := oneRowMatrixBound S v s
  have hB0 : 0 ≤ B := by dsimp [B, oneRowMatrixBound]; positivity
  have hm : Measurable (fun x : OneRowInput p => (1 + ‖x‖) ^ k) := by fun_prop
  apply oneRowInput_real_growth_integrable hq S
    (hm.fun_mul (hf.comp (measurable_oneRowWishartValue S (s • v))).norm)
    (C := C * (1 + B) ^ β) (β := (k : ℝ) + 2 * β) (by positivity)
  intro x
  have hx0 : 0 < 1 + ‖x‖ := by positivity
  have hW : 1 + ‖oneRowWishartValue S (s • v) x‖ ≤ (1 + B) * (1 + ‖x‖) ^ 2 := by
    have h := oneRowWishartValue_norm_bound S v s x
    change ‖oneRowWishartValue S (s • v) x‖ ≤ B * (1 + ‖x‖) ^ 2 at h
    nlinarith [norm_nonneg x]
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (1 + ‖x‖) ^ k * (C * ((1 + B) * (1 + ‖x‖) ^ 2) ^ β) := by
      gcongr
      exact (hB _).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hW hβ) hC)
    _ = (C * (1 + B) ^ β) * (1 + ‖x‖) ^ ((k : ℝ) + 2 * β) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast_mul hx0.le 2 β, ← Real.rpow_natCast,
        Real.rpow_add hx0]
      ring_nf

namespace BlockPartition

noncomputable def regularizedJetConstant {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε : ℝ) (k : ℕ) : ℝ :=
  match k with
  | 0 => 1
  | 1 => P.regularizedFirstConstant ν ε * coordinatesOperatorNorm p
  | 2 => (P.regularizedFirstConstant ν ε ^ 2 + P.regularizedSecondConstant ν ε) *
      coordinatesOperatorNorm p ^ 2
  | _ => 0

theorem regularizedJetConstant_nonneg {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    0 ≤ P.regularizedJetConstant ν ε k := by
  have hC₁ := P.regularizedFirstConstant_nonneg ν hε
  have hC₂ := P.regularizedSecondConstant_nonneg ν ε
  cases k with
  | zero => exact zero_le_one
  | succ k =>
      cases k with
      | zero => exact mul_nonneg hC₁ (coordinatesOperatorNorm_nonneg p)
      | succ k =>
          cases k with
          | zero => exact mul_nonneg (add_nonneg (sq_nonneg _) hC₂) (sq_nonneg _)
          | succ k => exact le_refl 0

theorem smoothProductEuclidean_jet_bound {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) {k : ℕ} (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (P.smoothProductEuclidean ν ε) (matrixCoordinates p W)‖ ≤
      ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν W‖ * P.regularizedJetConstant ν ε k := by
  interval_cases k
  · simpa only [regularizedJetConstant, mul_one] using
      (P.smoothProductEuclidean_jet_zero ν hε hW).le
  · simpa only [regularizedJetConstant, mul_assoc] using P.smoothProductEuclidean_jet_one ν hε hW
  · simpa only [regularizedJetConstant, mul_assoc] using P.smoothProductEuclidean_jet_two ν hε hW

theorem regularizedProduct_latent_weight_integrable {p d : ℕ} (P : BlockPartition p d)
    {q : ℝ} (hq : (p : ℝ) < q) (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s ε : ℝ)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) (k : ℕ) :
    Integrable (fun x : OneRowInput p => (1 + ‖x‖) ^ k *
      ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν
        (oneRowWishartValue S (s • v) x)‖) (oneRowInputLaw q S) := by
  apply oneRowInput_matrix_growth_integrable hq S v s
    (P.measurable_shiftedDeterminantProduct _ ν)
    (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (by positivity) (ν j))
    (Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hν j))
    (P.shiftedDeterminantProduct_growth _ ν hν) k

theorem regularizedProduct_coefficient_integrable {p d : ℕ} (P : BlockPartition p d)
    {q s : ℝ} (hq : (p : ℝ) < q) (hs : 0 < s)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (ε : ℝ)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) (i : WishartDifferentialIndex p) :
    Integrable (fun x => ‖wishartDifferenceCoefficient q S v s i x‖ *
      ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν
        (oneRowWishartValue S (s • v) x)‖) (oneRowInputLaw q S) := by
  apply ((P.regularizedProduct_latent_weight_integrable hq S v s ε ν hν 1).const_mul
    (wishartDifferenceBound q S v s)).mono' (by
      exact ((wishartDifferenceCoefficient_measurable q S v s i).norm.fun_mul
        ((P.measurable_shiftedDeterminantProduct _ ν).comp
          (measurable_oneRowWishartValue S (s • v))).norm).aestronglyMeasurable)
  exact ae_of_all _ fun x => by
    rw [Real.norm_of_nonneg (by
      have h := wishartDifferenceBound_nonneg q S v s
      positivity), pow_one]
    calc
      _ ≤ (wishartDifferenceBound q S v s * (1 + ‖x‖)) *
          ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν
            (oneRowWishartValue S (s • v) x)‖ :=
        mul_le_mul_of_nonneg_right (wishartDifferenceCoefficient_bound q S v hs i x) (norm_nonneg _)
      _ = _ := by ring_nf

end BlockPartition
end ResearchMain.WishartBlocks
