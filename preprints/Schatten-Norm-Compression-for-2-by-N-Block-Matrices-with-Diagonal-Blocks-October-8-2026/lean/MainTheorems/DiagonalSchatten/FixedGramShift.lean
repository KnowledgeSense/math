import MainTheorems.DiagonalSchatten.RayShift
import MainTheorems.DiagonalSchatten.PowerRadialVariation

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

theorem powerQuadratic_shift (r t : ℝ) (m Z : Fin 3 → ℝ)
    (hm : 0 < m 0) (hdet : 0 < m 0 * m 1 - m 2 ^ 2) (hc : m 2 ≠ 0) :
    symmetricTraceProduct (Z + t • m) (symmetricPowerVariation r m (Z + t • m)) =
      symmetricTraceProduct Z (symmetricPowerVariation r m Z) +
        2 * t * r * symmetricTraceProduct Z (symmetricPower r m) +
        t ^ 2 * r * symmetricTraceProduct m (symmetricPower r m) := by
  rw [symmetricPowerVariation_add r m Z (t • m) hc,
    symmetricPowerVariation_smul r t m m hc, symmetricPowerVariation_radial r m hm hdet hc]
  have hcross := symmetricPowerVariation_trace_symmetric r m Z m hc
  rw [symmetricPowerVariation_radial r m hm hdet hc] at hcross
  have he : symmetricTraceProduct m (symmetricPowerVariation r m Z) =
      r * symmetricTraceProduct Z (symmetricPower r m) := by
    rw [← hcross]
    unfold symmetricTraceProduct
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  unfold symmetricTraceProduct at he ⊢
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination t * he

variable {J : Type*} [Fintype J]

theorem sum_column_quadratic (X : Matrix (Fin 2) J ℝ) (Z : Fin 3 → ℝ) :
    (∑ j, (Z 0 * X 0 j ^ 2 + 2 * Z 2 * X 0 j * X 1 j + Z 1 * X 1 j ^ 2)) =
      symmetricTraceProduct Z (gramCoordinates X) := by
  dsimp [symmetricTraceProduct, gramCoordinates]
  simp only [gramFirst, gramSecond, gramCross,
    Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
  ring

theorem RayParameters.sum_shift (g : RayParameters) (t : ℝ)
    (X : Matrix (Fin 2) J ℝ) (hk : g.k ≠ 0)
    (hD : ∀ j, X 0 j ≠ 0 ∨ X 1 j ≠ 0 → g.denominator (fun i => X i j) ≠ 0) :
    (∑ j, (g.shift t).functional (fun i => X i j)) =
      (∑ j, g.functional (fun i => X i j)) +
        (2 * t / g.k) * symmetricTraceProduct ![g.z1, g.z2, g.z12] (gramCoordinates X) +
        (t ^ 2 / g.k) * symmetricTraceProduct ![g.a, g.b, g.c] (gramCoordinates X) := by
  have hcol (j : J) : (g.shift t).functional (fun i => X i j) =
      g.functional (fun i => X i j) +
        (2 * t / g.k) * (g.z1 * X 0 j ^ 2 + 2 * g.z12 * X 0 j * X 1 j + g.z2 * X 1 j ^ 2) +
        (t ^ 2 / g.k) * (g.a * X 0 j ^ 2 + 2 * g.c * X 0 j * X 1 j + g.b * X 1 j ^ 2) := by
    by_cases hn : X 0 j ≠ 0 ∨ X 1 j ≠ 0
    · exact g.shift_functional t _ hk (hD j hn)
    · have h0 : X 0 j = 0 := by
        by_contra h
        exact hn (Or.inl h)
      have h1 : X 1 j = 0 := by
        by_contra h
        exact hn (Or.inr h)
      simp [RayParameters.functional, RayParameters.numerator, RayParameters.image, h0, h1]
  simp_rw [hcol]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [← sum_column_quadratic X ![g.z1, g.z2, g.z12],
    ← sum_column_quadratic X ![g.a, g.b, g.c]]
  simp

theorem RayParameters.fixedGram_shift_difference (g : RayParameters) (t : ℝ)
    (X : Matrix (Fin 2) J ℝ) (hk : g.k ≠ 0) (ha : 0 < g.a)
    (hd : 0 < g.a * g.b - g.c ^ 2) (hc : g.c ≠ 0)
    (hM : gramCoordinates X = symmetricPower (2 / g.k) ![g.a, g.b, g.c])
    (hD : ∀ j, X 0 j ≠ 0 ∨ X 1 j ≠ 0 → g.denominator (fun i => X i j) ≠ 0) :
    (∑ j, (g.shift t).functional (fun i => X i j)) -
        symmetricTraceProduct ![(g.shift t).z1, (g.shift t).z2, (g.shift t).z12]
          (symmetricPowerVariation (2 / g.k) ![g.a, g.b, g.c]
            ![(g.shift t).z1, (g.shift t).z2, (g.shift t).z12]) / 2 =
      (∑ j, g.functional (fun i => X i j)) -
        symmetricTraceProduct ![g.z1, g.z2, g.z12]
          (symmetricPowerVariation (2 / g.k) ![g.a, g.b, g.c] ![g.z1, g.z2, g.z12]) / 2 := by
  have hz : ![(g.shift t).z1, (g.shift t).z2, (g.shift t).z12] =
      (![g.z1, g.z2, g.z12] : Fin 3 → ℝ) + t • ![g.a, g.b, g.c] := by
    funext i
    fin_cases i <;> simp [RayParameters.shift]
  rw [g.sum_shift t X hk hD, hz, powerQuadratic_shift _ _ _ _ ha hd hc, hM]
  field_simp [hk]
  ring

end

end ResearchMain.DiagonalSchatten
