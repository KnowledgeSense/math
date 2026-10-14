import MainTheorems.DiagonalSchatten.ScaledSpectralFiniteRay
import MainTheorems.DiagonalSchatten.PositiveSpectralNormalization
import MainTheorems.DiagonalSchatten.CompressionRayShift

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J] [Nonempty J]

theorem finite_compression_ray_bound {p sign : ℝ}
    (hp : (2 < p ∧ p < 4 ∧ sign = 1) ∨ (1 < p ∧ p < 2 ∧ sign = -1))
    (X : Matrix (Fin 2) J ℝ) (Z : Fin 3 → ℝ) (hX : ∀ i j, 0 < X i j)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) :
    sign * (∑ j, (compressionRay p X Z).functional (fun i => X i j)) ≤
      sign * (inverseGramQuadratic p X Z / 2) := by
  let gamma := (p - 2) / 2
  let alpha := 2 / (p - 2)
  let M := gramCoordinates X
  let H := symmetricPower gamma M
  have hp2 : p ≠ 2 := by rcases hp with ⟨h, _, _⟩ | ⟨_, h, _⟩ <;> linarith
  have hg : gamma ≠ 0 := div_ne_zero (sub_ne_zero.mpr hp2) (by norm_num)
  have halpha : alpha = 1 / gamma := by dsimp [alpha, gamma]; field_simp
  have hpar : (1 < alpha ∧ sign = 1) ∨ (alpha < -2 ∧ sign = -1) := by
    rcases hp with ⟨h2, h4, rfl⟩ | ⟨h1, h2, rfl⟩
    · refine Or.inl ⟨?_, rfl⟩
      exact (lt_div_iff₀ (by linarith : 0 < p - 2)).mpr (by linarith)
    · refine Or.inr ⟨?_, rfl⟩
      exact (div_lt_iff_of_neg (by linarith : p - 2 < 0)).mpr (by linarith)
  have ha : alpha ≠ 0 := by rcases hpar with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have hA := positiveRows_gramFirst X hX
  have hC := positiveRows_gramCross X hX
  obtain ⟨hH0, _, hHd⟩ := symmetricPower_positive_definite gamma M hA hdet hC.ne'
  have hHcross : 0 < H 2 / alpha := by
    rcases hp with ⟨h2, _, _⟩ | ⟨_, h2, _⟩
    · have hc := symmetricPower_cross_positive (by dsimp [gamma]; linarith : 0 < gamma) M hA hdet hC
      have hap : 0 < alpha := div_pos (by norm_num) (by linarith)
      exact div_pos hc hap
    · have hc := symmetricPower_cross_negative (by dsimp [gamma]; linarith : gamma < 0) M hA hdet hC
      have han : alpha < 0 := div_neg_of_pos_of_neg (by norm_num) (by linarith)
      exact div_pos_of_neg_of_neg hc han
  have hHc : H 2 ≠ 0 := by intro h; simp [h] at hHcross
  obtain ⟨u, t, theta, s, hu, ht, ht1, htheta, htheta1, hs, hH⟩ :=
    positive_spectral_normalization H hH0 hHd hHc
  let N := twoSpectralMatrix t theta (s * Real.sqrt (theta * (1 - theta)))
  change H = u • N at hH
  have hN : N = ![spectralFirst t theta, spectralSecond t theta, spectralCross s t theta] :=
    twoSpectralMatrix_spectral t theta s
  have hcross : 0 < spectralCross s t theta / alpha := by
    have he : H 2 / alpha = u * (spectralCross s t theta / alpha) := by
      rw [hH, hN]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
      ring
    rw [he] at hHcross
    exact (mul_pos_iff_of_pos_left hu).mp hHcross
  have hNc : N 2 ≠ 0 := by
    intro h
    have he : H 2 = u * N 2 := congrFun hH 2
    rw [h] at he
    exact hHc (by simpa using he)
  have hNd : 0 < N 0 * N 1 - N 2 ^ 2 := by
    rw [hN]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    rw [spectral_determinant hs htheta.le htheta1.le]
    exact ht
  have hN0 : 0 < N 0 := by rw [hN]; exact spectralFirst_pos ht htheta.le htheta1.le
  have hq : (s * Real.sqrt (theta * (1 - theta))) ^ 2 = theta * (1 - theta) := by
    rw [mul_pow, hs, Real.sq_sqrt (mul_nonneg htheta.le (sub_nonneg.mpr htheta1.le)), one_mul]
  have hM : M = u ^ alpha • twoSpectralMatrix (t ^ alpha) theta
      (s * Real.sqrt (theta * (1 - theta))) := by
    have hi := symmetricPower_inverse hg M hA hdet hC.ne'
    rw [← halpha] at hi
    change symmetricPower alpha H = M at hi
    rw [hH, symmetricPower_scale hu alpha N hN0 hNd hNc,
      twoSpectralMatrix_power (ne_of_lt ht1) hq] at hi
    exact hi.symm
  have hMA : gramFirst X = u ^ alpha * spectralFirst (t ^ alpha) theta := by
    have he := congrFun hM 0
    simpa [M, gramCoordinates, twoSpectralMatrix_spectral] using he
  have hMB : gramSecond X = u ^ alpha * spectralSecond (t ^ alpha) theta := by
    have he := congrFun hM 1
    simpa [M, gramCoordinates, twoSpectralMatrix_spectral] using he
  have hMC : gramCross X = u ^ alpha * spectralCross s (t ^ alpha) theta := by
    have he := congrFun hM 2
    simpa [M, gramCoordinates, twoSpectralMatrix_spectral] using he
  have hnormalizedCross : 0 < spectralCross s (t ^ alpha) theta := by
    rw [hMC] at hC
    exact (mul_pos_iff_of_pos_left (Real.rpow_pos_of_pos hu alpha)).mp hC
  have hcoeff : realGramPowerCoefficient gamma X = u • N := by
    rw [← symmetricPower_gram]
    exact hH
  have hk : p - 2 = 2 / alpha := by dsimp only [alpha]; field_simp [sub_ne_zero.mpr hp2]
  have hgRay : compressionRay p X Z = (spectralRay alpha t theta s Z).scale u := by
    unfold compressionRay
    rw [hcoeff, hN]
    unfold RayParameters.scale spectralRay
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hk]
  have hR : inverseGramQuadratic p X Z =
      symmetricTraceProduct Z (symmetricPowerVariation alpha (u • N) Z) := by
    unfold inverseGramQuadratic
    rw [← halpha]
    change symmetricTraceProduct Z (symmetricPowerVariation alpha H Z) = _
    rw [hH]
  rw [hgRay, hR]
  exact scaled_spectral_finite_ray_bound hpar hu ht ht1 hs htheta htheta1 hcross
    hnormalizedCross X (fun i j => (hX i j).le) hMA hMB hMC Z

end

end ResearchMain.DiagonalSchatten
