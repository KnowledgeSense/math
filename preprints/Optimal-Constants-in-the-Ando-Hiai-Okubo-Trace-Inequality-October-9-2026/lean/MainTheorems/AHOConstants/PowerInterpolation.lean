import MainTheorems.AHOConstants.Interpolation
import MainTheorems.AHOConstants.BoundaryPowers
import MainTheorems.AHOConstants.HalfPowerTrace
import MainTheorems.AHOConstants.UnitaryTrace

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open ResearchMain.DiagonalSchatten

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def powerTraceInterpolant {A B Y : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hY : Y.PosDef) (U : Matrix I I ℂ) (z : ℂ) : ℂ :=
  Matrix.trace (U * complexPower hA (z / 2) * complexPower hB (z / 2) *
    complexPower hY (1 - z / 2))

theorem powerTraceInterpolant_differentiable {A B Y : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hY : Y.PosDef) (U : Matrix I I ℂ) :
    Differentiable ℂ (powerTraceInterpolant hA hB hY U) := by
  have hf : Differentiable ℂ (fun z : ℂ => z / 2) := differentiable_id.div_const 2
  have hg : Differentiable ℂ (fun z : ℂ => 1 - z / 2) :=
    (differentiable_const (c := (1 : ℂ))).sub hf
  have h₁ := (complexPower_differentiable hA).comp hf
  have h₂ := (complexPower_differentiable hB).comp hf
  have h₃ := (complexPower_differentiable hY).comp hg
  let T : Matrix I I ℂ →L[ℂ] ℂ :=
    (Matrix.traceLinearMap I ℂ ℂ).toContinuousLinearMap
  exact T.differentiable.comp ((((differentiable_const (c := U)).mul h₁).mul h₂).mul h₃)

theorem powerTraceInterpolant_stripBounded {A B Y : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hY : Y.PosDef) (U : Matrix I I ℂ) :
    StripBounded (powerTraceInterpolant hA hB hY U) := by
  have hf : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (z / 2).re ∧ (z / 2).re ≤ 1 := by
    intro z hz₀ hz₁
    have hr : (z / 2).re = z.re / 2 := by simp
    rw [hr]
    constructor <;> linarith
  have hg : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (1 - z / 2).re ∧ (1 - z / 2).re ≤ 1 := by
    intro z hz₀ hz₁
    have hr : (1 - z / 2).re = 1 - z.re / 2 := by simp
    rw [hr]
    constructor <;> linarith
  exact ((((StripBounded.constant U).mul
    ((complexPower_stripBounded hA).comp (fun z => z / 2) hf)).mul
    ((complexPower_stripBounded hB).comp (fun z => z / 2) hf)).mul
    ((complexPower_stripBounded hY).comp (fun z => 1 - z / 2) hg)).trace

theorem powerTraceInterpolant_zero_boundary {A B Y U : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hY : Y.PosDef)
    (hU : U ∈ unitary (Matrix I I ℂ)) {z : ℂ} (hz : z.re = 0) :
    ‖powerTraceInterpolant hA hB hY U z‖ ≤ (Matrix.trace Y).re := by
  let K := complexPower hA (z / 2) * complexPower hB (z / 2)
  let V := complexPower hY (((1 - z / 2).im : ℂ) * Complex.I)
  have hK : K ∈ unitary (Matrix I I ℂ) := complexPower_product_zero_boundary hA hB hz
  have hV : V ∈ unitary (Matrix I I ℂ) := complexPower_imaginary_unitary hY _
  have hr : (1 - z / 2).re = 1 := by simp [hz]
  have he : powerTraceInterpolant hA hB hY U z =
      Matrix.trace ((V * (U * K)) * Y) := by
    unfold powerTraceInterpolant
    rw [complexPower_vertical_line hY, hr, spectralPower_one Y hY.posSemidef]
    change Matrix.trace (U * complexPower hA (z / 2) * complexPower hB (z / 2) *
      (Y * V)) = _
    calc
      _ = Matrix.trace ((U * K * Y) * V) := by simp only [K, Matrix.mul_assoc]
      _ = Matrix.trace (V * (U * K * Y)) := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [he]
  exact unitary_positive_trace_bound ((unitary (Matrix I I ℂ)).mul_mem hV
    ((unitary (Matrix I I ℂ)).mul_mem hU hK)) hY.posSemidef

theorem powerTraceInterpolant_one_boundary {A B Y U : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hY : Y.PosDef)
    (hU : U ∈ unitary (Matrix I I ℂ)) {z : ℂ} (hz : z.re = 1) :
    ‖powerTraceInterpolant hA hB hY U z‖ ≤
      schattenNorm 2 (spectralPower A (1 / 2) * spectralPower B (1 / 2)) *
      schattenNorm 2 (spectralPower Y (1 / 2)) := by
  have hr : (1 - z / 2).re = 1 / 2 := by simp [hz]; norm_num
  have h := trace_product_hilbertSchmidt
    (U * (complexPower hA (z / 2) * complexPower hB (z / 2)))
    (complexPower hY (1 - z / 2))
  rw [schattenNorm_unitary_left hU,
    complexPower_product_half_boundary hA hB hz,
    complexPower_half_boundary hY hr] at h
  simpa only [powerTraceInterpolant, Matrix.mul_assoc] using h

end ResearchMain.AHOConstants
