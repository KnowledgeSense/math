import MainTheorems.DiagonalSchatten.SpectralResidualEndpoints
import MainTheorems.DiagonalSchatten.ResidualInterval

namespace ResearchMain.DiagonalSchatten

noncomputable section

theorem spectral_residual_interval_sign {alpha t theta s sign : ℝ}
    (ha : (1 < alpha ∧ sign = 1) ∨ (alpha < -2 ∧ sign = -1))
    (ht : 0 < t) (ht1 : t < 1) (hs : s ^ 2 = 1)
    (h0 : 0 < theta) (h1 : theta < 1)
    (hc : 0 < spectralCross s t theta / alpha)
    (hC : 0 < spectralCross s (t ^ alpha) theta) :
    ∀ r ∈ Set.Icc
      (spectralCross s (t ^ alpha) theta / spectralFirst (t ^ alpha) theta)
      (spectralSecond (t ^ alpha) theta / spectralCross s (t ^ alpha) theta), ∀ x y,
      0 ≤ sign * ((spectralResidual alpha t theta s).first r * x ^ 2 +
        2 * (spectralResidual alpha t theta s).offDiagonal r * x * y +
        (spectralResidual alpha t theta s).second r * y ^ 2) := by
  have har : 1 < alpha ∨ alpha < -2 := ha.imp And.left And.left
  have hac : 1 < alpha ∨ alpha ≤ -2 := har.imp id le_of_lt
  have han : alpha ≠ 0 := by rcases har with h | h <;> linarith
  have hsign : sign = 1 ∨ sign = -1 := ha.imp And.right And.right
  let g := spectralResidual alpha t theta s
  let A := spectralFirst (t ^ alpha) theta
  let B := spectralSecond (t ^ alpha) theta
  let C := spectralCross s (t ^ alpha) theta
  let l := C / A
  let r := B / C
  have htp := Real.rpow_pos_of_pos ht alpha
  have hA : 0 < A := spectralFirst_pos htp h0.le h1.le
  have hB : 0 < B := spectralSecond_pos htp h0.le h1.le
  have hCp : 0 < C := hC
  have hdet : 0 < A * B - C ^ 2 := by
    dsimp only [A, B, C]
    rw [spectral_determinant hs h0.le h1.le]
    exact htp
  have hl : 0 < l := div_pos hCp hA
  have hlr : l < r := by
    apply (div_lt_div_iff₀ hA hCp).mpr
    nlinarith
  have hk : g.k ≠ 0 := div_ne_zero (by norm_num) han
  have hk1 : 0 < g.k + 1 := by
    change 0 < 2 / alpha + 1
    rcases har with h | h
    · have hk := div_pos (by norm_num : (0 : ℝ) < 2) (by linarith : 0 < alpha)
      linarith
    · have hk := (lt_div_iff_of_neg (by linarith : alpha < 0)).mpr
        (by linarith : (2 : ℝ) < -1 * alpha)
      linarith
  have hcn : g.c ≠ 0 := by intro h; change spectralCross s t theta = 0 at h; simp [h] at hc
  have hD : ∀ z ∈ Set.Icc l r, 0 < g.denominator z := by
    intro z hz
    have hzpos : 0 < z := hl.trans_le hz.1
    have hd := spectralRay_denominator_positive har ht hs h0.le h1.le hc (0 : Fin 3 → ℝ)
      (![1, z] : Fin 2 → ℝ) (by norm_num) hzpos.le (Or.inl (by norm_num))
    simpa [g, spectralRay, spectralResidual, RayParameters.denominator,
      ResidualParameters.denominator] using hd
  obtain ⟨hlQ, hrQ⟩ := spectral_residual_endpoint_sign ha ht (ne_of_lt ht1) hs h0.le h1.le hc hC
  exact g.signed_interval_of_endpoints hsign hlr hl
    (spectralFirst_pos ht h0.le h1.le) (spectralSecond_pos ht h0.le h1.le).ne'
    hcn hC hk hk1.ne' (by linarith) hD
    (spectralResidual_leading_negative hac ht ht1 hs h0 h1 hc)
    (spectralResidual_balance_symmetric hac ht ht1 hs h0.le h1.le hC) hlQ hrQ

end

end ResearchMain.DiagonalSchatten
