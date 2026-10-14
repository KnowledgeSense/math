import MainTheorems.DiagonalSchatten.SpectralRayBound
import MainTheorems.DiagonalSchatten.EndpointRows

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

theorem spectral_residual_of_two_column {alpha t theta s sign r : ℝ}
    (ha : (1 < alpha ∧ sign = 1) ∨ (alpha < -2 ∧ sign = -1))
    (ht : 0 < t) (ht1 : t ≠ 1) (hs : s ^ 2 = 1)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hc : 0 < spectralCross s t theta / alpha)
    (hC : 0 < spectralCross s (t ^ alpha) theta) (hr : 0 < r)
    (T : Matrix (Fin 2) (Fin 2) ℝ) (hT : ∀ i j, 0 ≤ T i j)
    (hA : gramFirst T = spectralFirst (t ^ alpha) theta)
    (hB : gramSecond T = spectralSecond (t ^ alpha) theta)
    (hCT : gramCross T = spectralCross s (t ^ alpha) theta)
    (hobj : ∀ Z : Fin 3 → ℝ,
      columnObjective (spectralRay alpha t theta s Z).functional T =
        (spectralFirst (t ^ alpha) theta - spectralCross s (t ^ alpha) theta / r) *
          (spectralRay alpha t theta s Z).functional ![1, 0] +
        (spectralSecond (t ^ alpha) theta - spectralCross s (t ^ alpha) theta * r) *
          (spectralRay alpha t theta s Z).functional ![0, 1] +
        (spectralCross s (t ^ alpha) theta / r) *
          (spectralRay alpha t theta s Z).functional ![1, r]) :
    ∀ x y, 0 ≤ sign * ((spectralResidual alpha t theta s).first r * x ^ 2 +
      2 * (spectralResidual alpha t theta s).offDiagonal r * x * y +
      (spectralResidual alpha t theta s).second r * y ^ 2) := by
  have har : 1 < alpha ∨ alpha < -2 := ha.imp And.left And.left
  have han : alpha ≠ 0 := by rcases har with h | h <;> linarith
  have hq : (s * Real.sqrt (theta * (1 - theta))) ^ 2 = theta * (1 - theta) := by
    rw [mul_pow, hs, Real.sq_sqrt (mul_nonneg h0 (sub_nonneg.mpr h1)), one_mul]
  have hcn : spectralCross s t theta ≠ 0 := by
    intro h
    simp [h] at hc
  have hk : 2 / alpha ≠ 0 := div_ne_zero (by norm_num) han
  have hb : 2 / alpha + 1 ≠ 0 := by
    apply ne_of_gt
    rcases har with h | h
    · have hk := div_pos (by norm_num : (0 : ℝ) < 2) (by linarith : 0 < alpha)
      linarith
    · have hk := (lt_div_iff_of_neg (by linarith : alpha < 0)).mpr
        (by linarith : (2 : ℝ) < -1 * alpha)
      linarith
  intro x y
  let Z : Fin 3 → ℝ := ![x, y, 0]
  let g := spectralRay alpha t theta s Z
  have hD : g.denominator ![1, r] ≠ 0 :=
    (spectralRay_denominator_positive har ht hs h0 h1 hc Z _
      (by norm_num) hr.le (Or.inl (by norm_num))).ne'
  have hbound := spectral_two_column_bound ha ht ht1 hs h0 h1 hC T Z hT hA hB hCT
  change sign * columnObjective g.functional T ≤ _ at hbound
  rw [hobj Z] at hbound
  rw [spectral_diagonal_quadratic ht1 hq x y] at hbound
  have he := three_ray_residual g
    (spectralFirst (t ^ alpha) theta) (spectralSecond (t ^ alpha) theta)
    (spectralCross s (t ^ alpha) theta) (spectralQ11 alpha t theta)
    (spectralQ22 alpha t theta) (spectralQ12 alpha t theta) r
    (spectralFirst_pos ht h0 h1).ne' (spectralSecond_pos ht h0 h1).ne'
    hcn hk hb hr.ne' hD (by simp [g, spectralRay, Z])
  dsimp only [g] at he
  rw [spectralRay_residual Z] at he
  simp only [spectralRay, Z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    spectralQ11, spectralQ22, spectralQ12] at he hbound
  rw [← he]
  nlinarith [hbound]

theorem spectral_residual_endpoint_sign {alpha t theta s sign : ℝ}
    (ha : (1 < alpha ∧ sign = 1) ∨ (alpha < -2 ∧ sign = -1))
    (ht : 0 < t) (ht1 : t ≠ 1) (hs : s ^ 2 = 1)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hc : 0 < spectralCross s t theta / alpha)
    (hC : 0 < spectralCross s (t ^ alpha) theta) :
    (∀ x y, 0 ≤ sign * ((spectralResidual alpha t theta s).first
        (spectralCross s (t ^ alpha) theta / spectralFirst (t ^ alpha) theta) * x ^ 2 +
      2 * (spectralResidual alpha t theta s).offDiagonal
        (spectralCross s (t ^ alpha) theta / spectralFirst (t ^ alpha) theta) * x * y +
      (spectralResidual alpha t theta s).second
        (spectralCross s (t ^ alpha) theta / spectralFirst (t ^ alpha) theta) * y ^ 2)) ∧
    (∀ x y, 0 ≤ sign * ((spectralResidual alpha t theta s).first
        (spectralSecond (t ^ alpha) theta / spectralCross s (t ^ alpha) theta) * x ^ 2 +
      2 * (spectralResidual alpha t theta s).offDiagonal
        (spectralSecond (t ^ alpha) theta / spectralCross s (t ^ alpha) theta) * x * y +
      (spectralResidual alpha t theta s).second
        (spectralSecond (t ^ alpha) theta / spectralCross s (t ^ alpha) theta) * y ^ 2)) := by
  let A := spectralFirst (t ^ alpha) theta
  let B := spectralSecond (t ^ alpha) theta
  let C := spectralCross s (t ^ alpha) theta
  have htp := Real.rpow_pos_of_pos ht alpha
  have hAp : 0 < A := spectralFirst_pos htp h0 h1
  have hBp : 0 < B := spectralSecond_pos htp h0 h1
  have hCp : 0 < C := hC
  have hd : 0 < A * B - C ^ 2 := by
    dsimp only [A, B, C]
    rw [spectral_determinant hs h0 h1]
    exact htp
  obtain ⟨hL, hLA, hLB, hLC⟩ := firstEndpointRows_gram hAp hCp hd
  obtain ⟨hR, hRA, hRB, hRC⟩ := secondEndpointRows_gram hBp hCp hd
  constructor
  · exact spectral_residual_of_two_column ha ht ht1 hs h0 h1 hc hC (div_pos hCp hAp)
      (firstEndpointRows A B C) hL hLA hLB hLC
      (fun Z => firstEndpointRows_objective hAp hCp hd _
        (spectralRay alpha t theta s Z).functional_homogeneous)
  · exact spectral_residual_of_two_column ha ht ht1 hs h0 h1 hc hC (div_pos hBp hCp)
      (secondEndpointRows A B C) hR hRA hRB hRC
      (fun Z => secondEndpointRows_objective hBp hCp hd _
        (spectralRay alpha t theta s Z).functional_homogeneous)

end

end ResearchMain.DiagonalSchatten
