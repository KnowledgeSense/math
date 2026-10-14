import MainTheorems.WishartBlocks.DeterminantDerivatives
import MainTheorems.WishartBlocks.RankOneWishartLaw

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators

theorem covariance_precision_curve {p : ℕ}
    (S T H : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
    1 + (2 : ℝ) • (S * (T + t • H)) =
      (1 + (2 : ℝ) • (S * T)) + t • ((2 : ℝ) • (S * H)) := by
  simp only [Matrix.mul_add, Matrix.mul_smul, smul_add, smul_smul]
  module

theorem covariance_resolvent_trace_directional {p : ℕ}
    (S T H M : Matrix (Fin p) (Fin p) ℝ)
    (hD : (1 + (2 : ℝ) • (S * T)).det ≠ 0) :
    HasDerivAt
      (fun t : ℝ => ((T + t • H) *
        (1 + (2 : ℝ) • (S * (T + t • H)))⁻¹ * M).trace)
      (((1 + (2 : ℝ) • (S * T))⁻¹ * (M * H)).trace -
        ((1 + (2 : ℝ) • (S * T))⁻¹ * ((2 : ℝ) • (S * H)) *
          (1 + (2 : ℝ) • (S * T))⁻¹ * (M * T)).trace) 0 := by
  let P := 1 + (2 : ℝ) • (S * T)
  let J := (2 : ℝ) • (S * H)
  have he : ∀ t : ℝ, ((T + t • H) *
      (1 + (2 : ℝ) • (S * (T + t • H)))⁻¹ * M).trace =
      ((P + t • J)⁻¹ * (M * T)).trace +
        t * ((P + t • J)⁻¹ * (M * H)).trace := by
    intro t
    calc
      _ = (((P + t • J)⁻¹ * M) * (T + t • H)).trace := by
        rw [covariance_precision_curve, Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = _ := by
        simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
          Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  have h₁ := inverse_trace_directional P (M * T) J hD
  have h₂ := inverse_trace_directional P (M * H) J hD
  have h := h₁.add ((hasDerivAt_id' (0 : ℝ)).mul h₂)
  simp only [zero_smul, add_zero, zero_mul, one_mul, add_zero] at h
  convert h using 1
  · funext t
    exact he t
  · dsimp only [P, J]
    ring

noncomputable def oneRowLaplaceClosed {p : ℕ} (q : ℝ)
    (S T : Matrix (Fin p) (Fin p) ℝ) (m : EuclideanSpace ℝ (Fin p)) : ℝ :=
  (1 + (2 : ℝ) • (S * T)).det ^ (-q / 2) *
    Real.exp (-((T * (1 + (2 : ℝ) • (S * T))⁻¹) *
      Matrix.vecMulVec (fun i => m i) (fun i => m i)).trace)

noncomputable def oneRowLaplaceDirectionalCoefficient {p : ℕ} (q : ℝ)
    (S T H : Matrix (Fin p) (Fin p) ℝ) (m : EuclideanSpace ℝ (Fin p)) : ℝ :=
  let P := 1 + (2 : ℝ) • (S * T)
  let J := (2 : ℝ) • (S * H)
  let M := Matrix.vecMulVec (fun i => m i) (fun i => m i)
  (-q / 2) * (P⁻¹ * J).trace -
    ((P⁻¹ * (M * H)).trace - (P⁻¹ * J * P⁻¹ * (M * T)).trace)

theorem oneRowLaplaceClosed_eq_expectation {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    {S T : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hT : T.PosSemidef)
    (m : EuclideanSpace ℝ (Fin p)) :
    (∫ W, Real.exp (-Matrix.trace (T * W)) ∂(oneRowWishartLaw q S m)) =
      oneRowLaplaceClosed q S T m := by
  rw [oneRowWishart_laplace hq hS hT]
  simp only [oneRowLaplaceClosed, trace_vectorGram]

theorem oneRowLaplaceClosed_directional {p : ℕ} (q : ℝ)
    (S T H : Matrix (Fin p) (Fin p) ℝ) (m : EuclideanSpace ℝ (Fin p))
    (hD : 0 < (1 + (2 : ℝ) • (S * T)).det) :
    HasDerivAt (fun t : ℝ => oneRowLaplaceClosed q S (T + t • H) m)
      (oneRowLaplaceClosed q S T m * oneRowLaplaceDirectionalCoefficient q S T H m) 0 := by
  let P := 1 + (2 : ℝ) • (S * T)
  let J := (2 : ℝ) • (S * H)
  let M := Matrix.vecMulVec (fun i => m i) (fun i => m i)
  have hC : HasDerivAt (fun t : ℝ =>
      (1 + (2 : ℝ) • (S * (T + t • H))).det ^ (-q / 2))
      (P.det ^ (-q / 2) * ((-q / 2) * (P⁻¹ * J).trace)) 0 := by
    simpa only [covariance_precision_curve] using
      determinant_power_directional P J hD (-q / 2)
  have hE := (covariance_resolvent_trace_directional S T H M hD.ne').neg.exp
  have h := hC.mul hE
  convert h using 1
  · funext t
    rfl
  · simp only [Pi.neg_apply, zero_smul, add_zero]
    dsimp only [oneRowLaplaceClosed, oneRowLaplaceDirectionalCoefficient, P, J, M]
    ring

end ResearchMain.WishartBlocks
