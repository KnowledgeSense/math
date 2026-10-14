import MainTheorems.DiagonalSchatten.CompressionHessianFormula
import MainTheorems.DiagonalSchatten.CompressionKernel

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

def symmetricTraceProduct (z w : Fin 3 → ℝ) : ℝ := z 0 * w 0 + z 1 * w 1 + 2 * z 2 * w 2

theorem entry_power_second_variation {p b : ℝ} (hp : p ≠ 0) (hb : 0 < b)
    (e u v : ℝ) :
    (v * b ^ (1 / p - 1) + u * ((1 / p - 1) * b ^ (1 / p - 2) * e)) * e =
      p * v * ((1 / p) * b ^ (1 / p - 1) * e) -
        p * (p - 1) * u * ((1 / p) * b ^ (1 / p - 1) * e) ^ 2 / b ^ (1 / p) := by
  have hx : b ^ (1 / p) ≠ 0 := (Real.rpow_pos_of_pos hb _).ne'
  have he : b ^ (1 / p - 2) * b ^ (1 / p) = (b ^ (1 / p - 1)) ^ 2 := by
    rw [← Real.rpow_add hb, ← Real.rpow_mul_natCast hb.le (1 / p - 1) 2]
    congr 1
    ring
  have hpow : b ^ (1 / p - 2) = (b ^ (1 / p - 1)) ^ 2 / b ^ (1 / p) :=
    (eq_div_iff hx).mpr he
  rw [hpow]
  field_simp [hp, hx]
  ring

variable {J : Type*} [Fintype J]

theorem gramVariation_trace_product (X Y : Matrix (Fin 2) J ℝ) (D : Fin 3 → ℝ) :
    (∑ j, ((D 0 * X 0 j + D 2 * X 1 j) * Y 0 j +
      (D 2 * X 0 j + D 1 * X 1 j) * Y 1 j)) =
      symmetricTraceProduct (gramVariation X Y) D / 2 := by
  calc
    _ = ∑ j, (D 0 * (X 0 j * Y 0 j) + D 1 * (X 1 j * Y 1 j) +
        D 2 * (Y 0 j * X 1 j + X 0 j * Y 1 j)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = D 0 * (∑ j, X 0 j * Y 0 j) + D 1 * (∑ j, X 1 j * Y 1 j) +
        D 2 * (∑ j, (Y 0 j * X 1 j + X 0 j * Y 1 j)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by
      change _ = ((2 * ∑ j, X 0 j * Y 0 j) * D 0 +
        (2 * ∑ j, X 1 j * Y 1 j) * D 1 +
        2 * (∑ j, (Y 0 j * X 1 j + X 0 j * Y 1 j)) * D 2) / 2
      ring

def compressionKernelEnergy (p : ℝ) (X Y : Matrix (Fin 2) J ℝ) : ℝ :=
  let H := realGramPowerCoefficient ((p - 2) / 2) X
  ∑ j, (kernelFirst (p - 2) (H 0) (H 2) (X 0 j) (X 1 j) * Y 0 j ^ 2 -
    2 * H 2 * Y 0 j * Y 1 j +
    kernelSecond (p - 2) (H 1) (H 2) (X 0 j) (X 1 j) * Y 1 j ^ 2)

variable [DecidableEq J] [Nonempty J]

theorem compressionHessian_second_variation {p : ℝ} (hp : 1 < p)
    (B E : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2) :
    let X := realEntryRoot p B
    let Y := entryRootDirection p B E
    compressionHessian p B E E = -p * compressionKernelEnergy p X Y +
      (p / 2) * symmetricTraceProduct (gramVariation X Y)
        (symmetricPowerVariation ((p - 2) / 2) (gramCoordinates X) (gramVariation X Y)) := by
  let X := realEntryRoot p B
  let Y := entryRootDirection p B E
  let H := realGramPowerCoefficient ((p - 2) / 2) X
  let D := symmetricPowerVariation ((p - 2) / 2) (gramCoordinates X) (gramVariation X Y)
  have hX : ∀ i j, 0 < X i j := fun i j => Real.rpow_pos_of_pos (hB i j) _
  have hp0 : p ≠ 0 := by linarith
  have hcol (j : J) :
      compressionGradientVariation p B E 0 j * E 0 j +
        compressionGradientVariation p B E 1 j * E 1 j =
      -p * (kernelFirst (p - 2) (H 0) (H 2) (X 0 j) (X 1 j) * Y 0 j ^ 2 -
        2 * H 2 * Y 0 j * Y 1 j +
        kernelSecond (p - 2) (H 1) (H 2) (X 0 j) (X 1 j) * Y 1 j ^ 2) +
      p * ((D 0 * X 0 j + D 2 * X 1 j) * Y 0 j +
        (D 2 * X 0 j + D 1 * X 1 j) * Y 1 j) := by
    have h0 := entry_power_second_variation hp0 (hB 0 j) (E 0 j)
      (H 0 * X 0 j + H 2 * X 1 j)
      (D 0 * X 0 j + D 2 * X 1 j + H 0 * Y 0 j + H 2 * Y 1 j)
    have h1 := entry_power_second_variation hp0 (hB 1 j) (E 1 j)
      (H 2 * X 0 j + H 1 * X 1 j)
      (D 2 * X 0 j + D 1 * X 1 j + H 2 * Y 0 j + H 1 * Y 1 j)
    change _ = p * (D 0 * X 0 j + D 2 * X 1 j + H 0 * Y 0 j + H 2 * Y 1 j) * Y 0 j -
      p * (p - 1) * (H 0 * X 0 j + H 2 * X 1 j) * Y 0 j ^ 2 / X 0 j at h0
    change _ = p * (D 2 * X 0 j + D 1 * X 1 j + H 2 * Y 0 j + H 1 * Y 1 j) * Y 1 j -
      p * (p - 1) * (H 2 * X 0 j + H 1 * X 1 j) * Y 1 j ^ 2 / X 1 j at h1
    change ((D 0 * X 0 j + D 2 * X 1 j + H 0 * Y 0 j + H 2 * Y 1 j) *
        B 0 j ^ (1 / p - 1) + (H 0 * X 0 j + H 2 * X 1 j) *
          ((1 / p - 1) * B 0 j ^ (1 / p - 2) * E 0 j)) * E 0 j +
      ((D 2 * X 0 j + D 1 * X 1 j + H 2 * Y 0 j + H 1 * Y 1 j) *
        B 1 j ^ (1 / p - 1) + (H 2 * X 0 j + H 1 * X 1 j) *
          ((1 / p - 1) * B 1 j ^ (1 / p - 2) * E 1 j)) * E 1 j = _
    rw [h0, h1]
    unfold kernelFirst kernelSecond
    field_simp [(hX 0 j).ne', (hX 1 j).ne']
    ring
  dsimp only
  rw [compressionHessian_gradientVariation hp B E hB hdet]
  simp_rw [hcol]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [gramVariation_trace_product X Y D]
  change -p * compressionKernelEnergy p X Y +
    p * (symmetricTraceProduct (gramVariation X Y) D / 2) = _
  ring

end

end ResearchMain.DiagonalSchatten
