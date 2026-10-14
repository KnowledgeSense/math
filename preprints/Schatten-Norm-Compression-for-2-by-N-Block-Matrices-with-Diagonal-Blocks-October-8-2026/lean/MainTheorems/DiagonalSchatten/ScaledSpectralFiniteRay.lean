import MainTheorems.DiagonalSchatten.SpectralFiniteRay
import MainTheorems.DiagonalSchatten.RayPowerScale

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

theorem scaled_spectral_finite_ray_bound {alpha t theta s sign u : ℝ}
    (ha : (1 < alpha ∧ sign = 1) ∨ (alpha < -2 ∧ sign = -1)) (hu : 0 < u)
    (ht : 0 < t) (ht1 : t < 1) (hs : s ^ 2 = 1)
    (h0 : 0 < theta) (h1 : theta < 1)
    (hc : 0 < spectralCross s t theta / alpha)
    (hC : 0 < spectralCross s (t ^ alpha) theta)
    (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (hA : gramFirst X = u ^ alpha * spectralFirst (t ^ alpha) theta)
    (hB : gramSecond X = u ^ alpha * spectralSecond (t ^ alpha) theta)
    (hCX : gramCross X = u ^ alpha * spectralCross s (t ^ alpha) theta) (Z : Fin 3 → ℝ) :
    sign * (∑ j, ((spectralRay alpha t theta s Z).scale u).functional (fun i => X i j)) ≤
      sign * (symmetricTraceProduct Z (symmetricPowerVariation alpha
        (u • twoSpectralMatrix t theta (s * Real.sqrt (theta * (1 - theta)))) Z) / 2) := by
  let v := Real.sqrt (u ^ alpha)
  let Y : Matrix (Fin 2) J ℝ := v⁻¹ • X
  let g := spectralRay alpha t theta s Z
  have hv : 0 < v := Real.sqrt_pos.mpr (Real.rpow_pos_of_pos hu alpha)
  have hv2 : v ^ 2 = u ^ alpha := Real.sq_sqrt (Real.rpow_nonneg hu.le alpha)
  have hY : ∀ i j, 0 ≤ Y i j := by
    intro i j
    exact mul_nonneg (inv_nonneg.mpr hv.le) (hX i j)
  have hcancel : (v⁻¹) ^ 2 * u ^ alpha = 1 := by rw [← hv2]; field_simp [hv.ne']
  have hYA : gramFirst Y = spectralFirst (t ^ alpha) theta := by
    rw [gramFirst_smul, hA, ← mul_assoc, hcancel, one_mul]
  have hYB : gramSecond Y = spectralSecond (t ^ alpha) theta := by
    rw [gramSecond_smul, hB, ← mul_assoc, hcancel, one_mul]
  have hYC : gramCross Y = spectralCross s (t ^ alpha) theta := by
    rw [gramCross_smul, hCX, ← mul_assoc, hcancel, one_mul]
  have hb := spectral_finite_ray_bound ha ht ht1 hs h0 h1 hc hC Y hY hYA hYB hYC Z
  have hscale : (∑ j, (g.scale u).functional (fun i => X i j)) =
      u ^ (alpha - 1) * ∑ j, g.functional (fun i => Y i j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hcol : (fun i => X i j) = v • (fun i => Y i j) := by
      funext i
      change X i j = v * (v⁻¹ * X i j)
      rw [← mul_assoc, mul_inv_cancel₀ hv.ne', one_mul]
    rw [g.scale_functional hu.ne', hcol, g.functional_homogeneous, hv2,
      Real.rpow_sub hu alpha 1, Real.rpow_one]
    ring
  have hH : ![g.a, g.b, g.c] =
      twoSpectralMatrix t theta (s * Real.sqrt (theta * (1 - theta))) :=
    (twoSpectralMatrix_spectral t theta s).symm
  have hdet : 0 < g.a * g.b - g.c ^ 2 := by
    change 0 < spectralFirst t theta * spectralSecond t theta - spectralCross s t theta ^ 2
    rw [spectral_determinant hs h0.le h1.le]
    exact ht
  have hcn : g.c ≠ 0 := by intro h; change spectralCross s t theta = 0 at h; simp [h] at hc
  have hvariation := symmetricPowerVariation_scale hu alpha ![g.a, g.b, g.c] Z
    (spectralFirst_pos ht h0.le h1.le) hdet hcn
  rw [hH] at hvariation
  rw [hscale, hvariation, symmetricTraceProduct_smul_right]
  have hpos := Real.rpow_pos_of_pos hu (alpha - 1)
  nlinarith [mul_le_mul_of_nonneg_left hb hpos.le]

end

end ResearchMain.DiagonalSchatten
