import MainTheorems.DiagonalSchatten.RayFunctional
import MainTheorems.DiagonalSchatten.GeneralResidual

namespace ResearchMain.DiagonalSchatten

noncomputable section

def rayResidual (g : RayParameters) (A B C q11 q22 q12 : ℝ) : ResidualParameters where
  a := g.a
  b := g.b
  c := g.c
  k := g.k
  cross := C
  u := q11 - A / (g.k * g.a)
  v := q22 - B / (g.k * g.b)
  w := q12

theorem rayResidual_denominator (g : RayParameters) (A B C q11 q22 q12 r : ℝ) :
    (rayResidual g A B C q11 q22 q12).denominator r = g.denominator ![1, r] := by
  unfold rayResidual ResidualParameters.denominator RayParameters.denominator
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem three_ray_residual (g : RayParameters) (A B C q11 q22 q12 r : ℝ)
    (ha : g.a ≠ 0) (hb : g.b ≠ 0) (hc : g.c ≠ 0)
    (hk : g.k ≠ 0) (hbeta : g.k + 1 ≠ 0) (hr : r ≠ 0)
    (hD : g.denominator ![1, r] ≠ 0) (hz : g.z12 = 0) :
    q11 * g.z1 ^ 2 + 2 * q12 * g.z1 * g.z2 + q22 * g.z2 ^ 2 -
        ((A - C / r) * g.functional ![1, 0] +
          (B - C * r) * g.functional ![0, 1] + (C / r) * g.functional ![1, r]) =
      (rayResidual g A B C q11 q22 q12).first r * g.z1 ^ 2 +
        2 * (rayResidual g A B C q11 q22 q12).offDiagonal r * g.z1 * g.z2 +
        (rayResidual g A B C q11 q22 q12).second r * g.z2 ^ 2 := by
  rw [g.functional_first_axis 1 hk ha hc hbeta, g.functional_second_axis 1 hk hb hc hbeta]
  simp only [one_pow, one_mul]
  have hd := rayResidual_denominator g A B C q11 q22 q12 r
  unfold ResidualParameters.first ResidualParameters.second ResidualParameters.offDiagonal
  rw [hd]
  unfold rayResidual RayParameters.functional RayParameters.numerator RayParameters.image
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hz, zero_mul,
    zero_add, add_zero, one_pow, mul_one]
  unfold RayParameters.denominator at hD ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one] at hD ⊢
  generalize hDval : g.k * ((g.k + 1) * g.a * g.c +
      (g.k * g.a * g.b + (g.k + 2) * g.c ^ 2) * r +
      (g.k + 1) * g.b * g.c * r ^ 2) = D
  have hDn : D ≠ 0 := by rw [← hDval]; exact hD
  field_simp [ha, hb, hk, hr, hDn]
  rw [← hDval]
  ring

end

end ResearchMain.DiagonalSchatten
