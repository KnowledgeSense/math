import MainTheorems.DiagonalSchatten.RayFunctional

namespace ResearchMain.DiagonalSchatten

noncomputable section

namespace RayParameters

def shift (g : RayParameters) (t : ℝ) : RayParameters :=
  { g with z1 := g.z1 + t * g.a, z2 := g.z2 + t * g.b, z12 := g.z12 + t * g.c }

theorem shift_denominator (g : RayParameters) (t : ℝ) (x : Fin 2 → ℝ) :
    (g.shift t).denominator x = g.denominator x := rfl

theorem shift_image (g : RayParameters) (t : ℝ) (x : Fin 2 → ℝ) :
    (g.shift t).image x = g.image x +
      t • (![g.a * x 0 + g.c * x 1, g.c * x 0 + g.b * x 1] : Fin 2 → ℝ) := by
  funext i
  fin_cases i
  · change (g.z1 + t * g.a) * x 0 + (g.z12 + t * g.c) * x 1 =
      g.z1 * x 0 + g.z12 * x 1 + t * (g.a * x 0 + g.c * x 1)
    ring
  · change (g.z12 + t * g.c) * x 0 + (g.z2 + t * g.b) * x 1 =
      g.z12 * x 0 + g.z2 * x 1 + t * (g.c * x 0 + g.b * x 1)
    ring

set_option maxHeartbeats 1500000 in
theorem shift_functional (g : RayParameters) (t : ℝ) (x : Fin 2 → ℝ)
    (hk : g.k ≠ 0) (hD : g.denominator x ≠ 0) :
    (g.shift t).functional x = g.functional x +
      (2 * t / g.k) * (g.z1 * x 0 ^ 2 + 2 * g.z12 * x 0 * x 1 + g.z2 * x 1 ^ 2) +
      (t ^ 2 / g.k) * (g.a * x 0 ^ 2 + 2 * g.c * x 0 * x 1 + g.b * x 1 ^ 2) := by
  unfold functional
  rw [g.shift_denominator]
  apply (div_eq_iff hD).mpr
  unfold numerator image shift
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold denominator at hD ⊢
  generalize hDval : g.k * ((g.k + 1) * g.a * g.c * x 0 ^ 2 +
      (g.k * g.a * g.b + (g.k + 2) * g.c ^ 2) * x 0 * x 1 +
      (g.k + 1) * g.b * g.c * x 1 ^ 2) = D
  have hDn : D ≠ 0 := by rw [← hDval]; exact hD
  field_simp [hk, hDn]
  rw [← hDval]
  ring

theorem shift_zero_offDiagonal (g : RayParameters) (hc : g.c ≠ 0) :
    (g.shift (-g.z12 / g.c)).z12 = 0 := by
  change g.z12 + (-g.z12 / g.c) * g.c = 0
  rw [div_mul_cancel₀ _ hc]
  ring

end RayParameters

end

end ResearchMain.DiagonalSchatten
