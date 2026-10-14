import MainTheorems.AHOConstants.PowerInterpolation
import MainTheorems.AHOConstants.PositiveTrace
import MainTheorems.AHOConstants.ScalarInterpolation

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open ResearchMain.DiagonalSchatten

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

theorem schattenPower_small_product {A B : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {r : ℝ} (hr : 0 < r) (hrh : r ≤ 1 / 2) :
    schattenPower (1 / r) (spectralPower A r * spectralPower B r) ≤
      (Matrix.trace (A * B)).re := by
  let X := spectralPower A r * spectralPower B r
  have hX : IsUnit X := (spectralPower_isUnit hA r).mul (spectralPower_isUnit hB r)
  let P := polarAbsolute X
  have hP : P.PosDef := polarAbsolute_posDef hX
  let Y := spectralPower P (1 / r)
  have hY : Y.PosDef := spectralPower_posDef hP (1 / r)
  let U := star (polarUnitary X)
  have hU : U ∈ unitary (Matrix I I ℂ) := Unitary.star_mem (polarUnitary_mem hX)
  have hUX : U * X = P := by
    change star (polarUnitary X) * X = polarAbsolute X
    calc
      _ = star (polarUnitary X) * (polarUnitary X * polarAbsolute X) := by
        rw [← polar_decomposition hX]
      _ = polarAbsolute X := by
        rw [← Matrix.mul_assoc, Unitary.star_mul_self_of_mem (polarUnitary_mem hX),
          Matrix.one_mul]
  have hYP : spectralPower Y (1 - r) = spectralPower P ((1 / r) * (1 - r)) :=
    spectralPower_iterate hP (1 / r) (1 - r) (by positivity)
  have hPY : P * spectralPower Y (1 - r) = Y := by
    rw [hYP]
    calc
      _ = spectralPower P 1 * spectralPower P ((1 / r) * (1 - r)) := by
        rw [spectralPower_one P hP.posSemidef]
      _ = spectralPower P (1 + (1 / r) * (1 - r)) :=
        (spectralPower_add_real hP _ _).symm
      _ = Y := by
        have he : 1 + (1 / r) * (1 - r) = 1 / r := by field_simp [hr.ne']; ring
        rw [he]
  have hvalue : powerTraceInterpolant hA hB hY U ((2 * r : ℝ) : ℂ) =
      Matrix.trace Y := by
    have he₁ : ((2 * r : ℝ) : ℂ) / 2 = (r : ℂ) := by push_cast; ring
    have he₂ : (1 : ℂ) - ((2 * r : ℝ) : ℂ) / 2 = ((1 - r : ℝ) : ℂ) := by
      push_cast; ring
    unfold powerTraceInterpolant
    rw [he₂, he₁, complexPower_real, complexPower_real, complexPower_real]
    change Matrix.trace ((U * spectralPower A r * spectralPower B r) *
      spectralPower Y (1 - r)) = _
    rw [Matrix.mul_assoc U, hUX, hPY]
  let D := (Matrix.trace (A * B)).re
  let T := (Matrix.trace Y).re
  let s := schattenNorm 2 (spectralPower A (1 / 2) * spectralPower B (1 / 2))
  let t := schattenNorm 2 (spectralPower Y (1 / 2))
  have hD : 0 < D := trace_product_positive hA hB
  have hT : 0 < T := positive_trace_pos hY
  have hs : 0 ≤ s := schattenNorm_nonneg 2 _
  have ht : 0 ≤ t := schattenNorm_nonneg 2 _
  have hsq : s ^ 2 = D := halfPower_product_norm_square hA.posSemidef hB.posSemidef
  have htq : t ^ 2 = T := halfPower_norm_square hY.posSemidef
  have hbound := scalar_three_lines (powerTraceInterpolant_differentiable hA hB hY U)
    (powerTraceInterpolant_stripBounded hA hB hY U)
    (t := 2 * r) (a := T) (b := s * t) (by positivity) (by linarith)
    (fun z hz => powerTraceInterpolant_zero_boundary hA hB hY hU hz)
    (fun z hz => powerTraceInterpolant_one_boundary hA hB hY hU hz)
  rw [hvalue, positive_trace_norm hY.posSemidef] at hbound
  have hTD : T ≤ D := trace_interpolation_scalar hT hD hs ht hr hsq htq hbound
  rw [schattenPower_eq_absolute_trace hX]
  exact hTD

theorem schattenNorm_small_product {A B : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {r : ℝ} (hr : 0 < r) (hrh : r ≤ 1 / 2) :
    schattenNorm (1 / r) (spectralPower A r * spectralPower B r) ≤
      (Matrix.trace (A * B)).re ^ r := by
  have h := schattenPower_small_product hA hB hr hrh
  unfold schattenNorm
  rw [one_div_one_div]
  exact Real.rpow_le_rpow (schattenPower_nonneg _ _) h hr.le

end ResearchMain.AHOConstants
