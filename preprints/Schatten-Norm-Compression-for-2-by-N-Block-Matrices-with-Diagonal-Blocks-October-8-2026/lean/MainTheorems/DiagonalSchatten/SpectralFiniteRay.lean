import MainTheorems.DiagonalSchatten.SpectralResidualInterval
import MainTheorems.DiagonalSchatten.FiniteRayBound
import MainTheorems.DiagonalSchatten.FixedGramShift

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

theorem spectral_diagonal_finite_ray_bound {alpha t theta s sign : ℝ}
    (ha : (1 < alpha ∧ sign = 1) ∨ (alpha < -2 ∧ sign = -1))
    (ht : 0 < t) (ht1 : t < 1) (hs : s ^ 2 = 1)
    (h0 : 0 < theta) (h1 : theta < 1)
    (hc : 0 < spectralCross s t theta / alpha)
    (hC : 0 < spectralCross s (t ^ alpha) theta)
    (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (hA : gramFirst X = spectralFirst (t ^ alpha) theta)
    (hB : gramSecond X = spectralSecond (t ^ alpha) theta)
    (hCX : gramCross X = spectralCross s (t ^ alpha) theta) (x y : ℝ) :
    sign * (∑ j, (spectralRay alpha t theta s ![x, y, 0]).functional (fun i => X i j)) ≤
      sign * (symmetricTraceProduct ![x, y, 0] (symmetricPowerVariation alpha
        (twoSpectralMatrix t theta (s * Real.sqrt (theta * (1 - theta)))) ![x, y, 0]) / 2) := by
  let Z : Fin 3 → ℝ := ![x, y, 0]
  let g := spectralRay alpha t theta s Z
  let R := symmetricTraceProduct Z (symmetricPowerVariation alpha
    (twoSpectralMatrix t theta (s * Real.sqrt (theta * (1 - theta)))) Z) / 2
  have har : 1 < alpha ∨ alpha < -2 := ha.imp And.left And.left
  have han : alpha ≠ 0 := by rcases har with h | h <;> linarith
  have htp := Real.rpow_pos_of_pos ht alpha
  have hmassA := spectralFirst_pos htp h0.le h1.le
  have hmassB := spectralSecond_pos htp h0.le h1.le
  have hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2 := by
    rw [hA, hB, hCX, spectral_determinant hs h0.le h1.le]
    exact htp
  have hcross : 0 < gramCross X := by rw [hCX]; exact hC
  have hcn : g.c ≠ 0 := by intro h; change spectralCross s t theta = 0 at h; simp [h] at hc
  have hk : g.k ≠ 0 := div_ne_zero (by norm_num) han
  have hbeta : g.k + 1 ≠ 0 := by
    apply ne_of_gt
    change 0 < 2 / alpha + 1
    rcases har with h | h
    · have hh := div_pos (by norm_num : (0 : ℝ) < 2) (by linarith : 0 < alpha)
      linarith
    · have hh := (lt_div_iff_of_neg (by linarith : alpha < 0)).mpr
        (by linarith : (2 : ℝ) < -1 * alpha)
      linarith
  have hq : (s * Real.sqrt (theta * (1 - theta))) ^ 2 = theta * (1 - theta) := by
    rw [mul_pow, hs, Real.sq_sqrt (mul_nonneg h0.le (sub_nonneg.mpr h1.le)), one_mul]
  have hR : R = spectralQ11 alpha t theta * x ^ 2 +
      2 * spectralQ12 alpha t theta * x * y + spectralQ22 alpha t theta * y ^ 2 :=
    spectral_diagonal_quadratic (ne_of_lt ht1) hq x y
  have hbound := g.finite_ray_bound X hX hcross hdet sign (sign * R)
    (fun z hz0 hz1 hz =>
      (spectralRay_denominator_positive har ht hs h0.le h1.le hc Z z hz0 hz1 hz).ne')
    (fun T hT hTA hTB hTC => by
      have hb := spectral_two_column_bound ha ht (ne_of_lt ht1) hs h0.le h1.le hC T Z hT
        (hTA.trans hA) (hTB.trans hB) (hTC.trans hCX)
      simpa only [columnObjective, ← Finset.mul_sum] using hb)
    (fun r hr => by
      have hri : r ∈ Set.Icc
          (spectralCross s (t ^ alpha) theta / spectralFirst (t ^ alpha) theta)
          (spectralSecond (t ^ alpha) theta / spectralCross s (t ^ alpha) theta) := by
        simpa only [hA, hB, hCX] using hr
      have hrpos : 0 < r := (div_pos hC hmassA).trans_le hri.1
      have hD : g.denominator ![1, r] ≠ 0 :=
        (spectralRay_denominator_positive har ht hs h0.le h1.le hc Z _
          (by norm_num) hrpos.le (Or.inl (by norm_num))).ne'
      have hquad := spectral_residual_interval_sign ha ht ht1 hs h0 h1 hc hC r hri x y
      have he := three_ray_residual g
        (spectralFirst (t ^ alpha) theta) (spectralSecond (t ^ alpha) theta)
        (spectralCross s (t ^ alpha) theta) (spectralQ11 alpha t theta)
        (spectralQ22 alpha t theta) (spectralQ12 alpha t theta) r
        (spectralFirst_pos ht h0.le h1.le).ne' (spectralSecond_pos ht h0.le h1.le).ne'
        hcn hk hbeta hrpos.ne' hD (by simp [g, spectralRay, Z])
      dsimp only [g] at he
      rw [spectralRay_residual Z] at he
      simp only [spectralRay, Z, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two] at he
      rw [← he] at hquad
      rw [hA, hB, hCX, hR]
      simp only [g, spectralRay, Z, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two] at hquad ⊢
      nlinarith [hquad])
  simpa only [columnObjective, ← Finset.mul_sum] using hbound

theorem spectral_finite_ray_bound {alpha t theta s sign : ℝ}
    (ha : (1 < alpha ∧ sign = 1) ∨ (alpha < -2 ∧ sign = -1))
    (ht : 0 < t) (ht1 : t < 1) (hs : s ^ 2 = 1)
    (h0 : 0 < theta) (h1 : theta < 1)
    (hc : 0 < spectralCross s t theta / alpha)
    (hC : 0 < spectralCross s (t ^ alpha) theta)
    (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (hA : gramFirst X = spectralFirst (t ^ alpha) theta)
    (hB : gramSecond X = spectralSecond (t ^ alpha) theta)
    (hCX : gramCross X = spectralCross s (t ^ alpha) theta) (Z : Fin 3 → ℝ) :
    sign * (∑ j, (spectralRay alpha t theta s Z).functional (fun i => X i j)) ≤
      sign * (symmetricTraceProduct Z (symmetricPowerVariation alpha
        (twoSpectralMatrix t theta (s * Real.sqrt (theta * (1 - theta)))) Z) / 2) := by
  let g := spectralRay alpha t theta s Z
  let shift := -g.z12 / g.c
  have har : 1 < alpha ∨ alpha < -2 := ha.imp And.left And.left
  have han : alpha ≠ 0 := by rcases har with h | h <;> linarith
  have hcn : g.c ≠ 0 := by intro h; change spectralCross s t theta = 0 at h; simp [h] at hc
  have hk : g.k ≠ 0 := div_ne_zero (by norm_num) han
  have hq : (s * Real.sqrt (theta * (1 - theta))) ^ 2 = theta * (1 - theta) := by
    rw [mul_pow, hs, Real.sq_sqrt (mul_nonneg h0.le (sub_nonneg.mpr h1.le)), one_mul]
  have hH : ![g.a, g.b, g.c] =
      twoSpectralMatrix t theta (s * Real.sqrt (theta * (1 - theta))) :=
    (twoSpectralMatrix_spectral t theta s).symm
  have hZ : ![g.z1, g.z2, g.z12] = Z := by
    funext i
    fin_cases i <;> simp [g, spectralRay]
  have he : 2 / g.k = alpha := by change 2 / (2 / alpha) = _; field_simp [han]
  have hM : gramCoordinates X = symmetricPower (2 / g.k) ![g.a, g.b, g.c] := by
    rw [he, hH, twoSpectralMatrix_power (ne_of_lt ht1) hq, twoSpectralMatrix_spectral]
    funext i
    fin_cases i <;> simp [gramCoordinates, hA, hB, hCX]
  have hD (j : J) (hn : X 0 j ≠ 0 ∨ X 1 j ≠ 0) :
      g.denominator (fun i => X i j) ≠ 0 := by
    apply (spectralRay_denominator_positive har ht hs h0.le h1.le hc Z _
      (hX 0 j) (hX 1 j) ?_).ne'
    rcases hn with hn | hn
    · exact Or.inl (lt_of_le_of_ne (hX 0 j) (Ne.symm hn))
    · exact Or.inr (lt_of_le_of_ne (hX 1 j) (Ne.symm hn))
  have hdet : 0 < g.a * g.b - g.c ^ 2 := by
    change 0 < spectralFirst t theta * spectralSecond t theta - spectralCross s t theta ^ 2
    rw [spectral_determinant hs h0.le h1.le]
    exact ht
  have hshift : g.shift shift = spectralRay alpha t theta s
      ![(g.shift shift).z1, (g.shift shift).z2, 0] := by
    dsimp only [g, RayParameters.shift, spectralRay]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    congr 1
    exact g.shift_zero_offDiagonal hcn
  have hbound := spectral_diagonal_finite_ray_bound ha ht ht1 hs h0 h1 hc hC X hX hA hB hCX
    (g.shift shift).z1 (g.shift shift).z2
  rw [← hshift] at hbound
  have hdiff := g.fixedGram_shift_difference shift X hk
    (spectralFirst_pos ht h0.le h1.le) hdet hcn hM hD
  rw [he, hH, hZ] at hdiff
  have hz : ![(g.shift shift).z1, (g.shift shift).z2, (g.shift shift).z12] =
      (![ (g.shift shift).z1, (g.shift shift).z2, 0] : Fin 3 → ℝ) := by
    rw [g.shift_zero_offDiagonal hcn]
  rw [hz] at hdiff
  nlinarith [hbound, congrArg (fun v : ℝ => sign * v) hdiff]

end

end ResearchMain.DiagonalSchatten
