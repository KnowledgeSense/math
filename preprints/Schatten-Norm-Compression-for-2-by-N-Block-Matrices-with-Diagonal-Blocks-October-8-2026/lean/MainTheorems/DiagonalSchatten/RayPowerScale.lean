import MainTheorems.DiagonalSchatten.SymmetricPowerScale
import MainTheorems.DiagonalSchatten.RayFunctional

namespace ResearchMain.DiagonalSchatten

noncomputable section

namespace RayParameters

def scale (g : RayParameters) (c : ℝ) : RayParameters where
  a := c * g.a
  b := c * g.b
  c := c * g.c
  k := g.k
  z1 := g.z1
  z2 := g.z2
  z12 := g.z12

theorem scale_numerator (g : RayParameters) (c : ℝ) (x : Fin 2 → ℝ) :
    (g.scale c).numerator x = c * g.numerator x := by
  simp only [numerator, image, scale, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem scale_denominator (g : RayParameters) (c : ℝ) (x : Fin 2 → ℝ) :
    (g.scale c).denominator x = c ^ 2 * g.denominator x := by
  unfold denominator scale
  ring

theorem scale_functional (g : RayParameters) {c : ℝ} (hc : c ≠ 0) (x : Fin 2 → ℝ) :
    (g.scale c).functional x = c⁻¹ * g.functional x := by
  unfold functional
  rw [g.scale_numerator, g.scale_denominator]
  rw [pow_two, mul_assoc, mul_div_mul_left _ _ hc]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end RayParameters

end

end ResearchMain.DiagonalSchatten
