import MainTheorems.DiagonalSchatten.SpectralDiagonalQuadratic
import MainTheorems.DiagonalSchatten.PowerInverseIdentity
import MainTheorems.DiagonalSchatten.CompressionRayParameters
import MainTheorems.DiagonalSchatten.ThreeRayResidual
import MainTheorems.DiagonalSchatten.TwoColumnRayBoundary

namespace ResearchMain.DiagonalSchatten

noncomputable section

def spectralRay (alpha t theta s : ℝ) (Z : Fin 3 → ℝ) : RayParameters where
  a := spectralFirst t theta
  b := spectralSecond t theta
  c := spectralCross s t theta
  k := 2 / alpha
  z1 := Z 0
  z2 := Z 1
  z12 := Z 2

def spectralQ11 (alpha t theta : ℝ) : ℝ :=
  (alpha * theta ^ 2 + alpha * t ^ (alpha - 1) * (1 - theta) ^ 2 +
    2 * ((1 - t ^ alpha) / (1 - t)) * theta * (1 - theta)) / 2

def spectralQ22 (alpha t theta : ℝ) : ℝ :=
  (alpha * (1 - theta) ^ 2 + alpha * t ^ (alpha - 1) * theta ^ 2 +
    2 * ((1 - t ^ alpha) / (1 - t)) * theta * (1 - theta)) / 2

def spectralQ12 (alpha t theta : ℝ) : ℝ :=
  theta * (1 - theta) *
    (alpha * (1 + t ^ (alpha - 1)) - 2 * ((1 - t ^ alpha) / (1 - t))) / 2

theorem twoSpectralMatrix_spectral (t theta s : ℝ) :
    twoSpectralMatrix t theta (s * Real.sqrt (theta * (1 - theta))) =
      ![spectralFirst t theta, spectralSecond t theta, spectralCross s t theta] := by
  funext i
  fin_cases i <;> simp [twoSpectralMatrix, orderedSpectralMatrix,
    spectralFirst, spectralSecond, spectralCross] <;> ring

theorem spectralRay_residual {alpha t theta s : ℝ} (Z : Fin 3 → ℝ) :
    rayResidual (spectralRay alpha t theta s Z)
      (spectralFirst (t ^ alpha) theta) (spectralSecond (t ^ alpha) theta)
      (spectralCross s (t ^ alpha) theta) (spectralQ11 alpha t theta)
      (spectralQ22 alpha t theta) (spectralQ12 alpha t theta) =
        spectralResidual alpha t theta s := by
  unfold rayResidual spectralRay spectralResidual spectralQ11 spectralQ22 spectralQ12
  congr 1 <;> simp only [div_eq_mul_inv, mul_inv_rev, inv_inv] <;> ring

variable {J : Type*} [Fintype J]

theorem compressionRay_spectral {alpha t theta s : ℝ}
    (ha : alpha ≠ 0) (ht : 0 < t) (ht1 : t ≠ 1)
    (hs : s ^ 2 = 1) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (X : Matrix (Fin 2) J ℝ) (Z : Fin 3 → ℝ)
    (hA : gramFirst X = spectralFirst (t ^ alpha) theta)
    (hB : gramSecond X = spectralSecond (t ^ alpha) theta)
    (hC : gramCross X = spectralCross s (t ^ alpha) theta) :
    compressionRay (2 + 2 / alpha) X Z = spectralRay alpha t theta s Z := by
  have hq : (s * Real.sqrt (theta * (1 - theta))) ^ 2 = theta * (1 - theta) := by
    rw [mul_pow, hs, Real.sq_sqrt (mul_nonneg h0 (sub_nonneg.mpr h1)), one_mul]
  have htalpha : t ^ alpha ≠ 1 := by
    intro he
    apply ht1
    exact (Real.rpow_left_inj ht.le zero_le_one ha).mp (by simpa using he)
  have he : (2 + 2 / alpha - 2) / 2 = 1 / alpha := by ring
  have hroot : (t ^ alpha) ^ (1 / alpha) = t := by
    rw [← Real.rpow_mul ht.le, show alpha * (1 / alpha) = 1 by field_simp [ha], Real.rpow_one]
  have hpower : realGramPowerCoefficient ((2 + 2 / alpha - 2) / 2) X =
      ![spectralFirst t theta, spectralSecond t theta, spectralCross s t theta] := by
    rw [← symmetricPower_gram, hA, hB, hC, he, ← twoSpectralMatrix_spectral,
      twoSpectralMatrix_power htalpha hq, hroot, twoSpectralMatrix_spectral]
  unfold compressionRay spectralRay
  rw [hpower]
  congr 1
  simp

theorem inverseGramQuadratic_spectral {alpha t theta s : ℝ}
    (ha : alpha ≠ 0) (ht : 0 < t) (ht1 : t ≠ 1)
    (hs : s ^ 2 = 1) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (X : Matrix (Fin 2) J ℝ) (Z : Fin 3 → ℝ)
    (hA : gramFirst X = spectralFirst (t ^ alpha) theta)
    (hB : gramSecond X = spectralSecond (t ^ alpha) theta)
    (hC : gramCross X = spectralCross s (t ^ alpha) theta) :
    inverseGramQuadratic (2 + 2 / alpha) X Z =
      symmetricTraceProduct Z (symmetricPowerVariation alpha
        (twoSpectralMatrix t theta (s * Real.sqrt (theta * (1 - theta)))) Z) := by
  have hq : (s * Real.sqrt (theta * (1 - theta))) ^ 2 = theta * (1 - theta) := by
    rw [mul_pow, hs, Real.sq_sqrt (mul_nonneg h0 (sub_nonneg.mpr h1)), one_mul]
  have htalpha : t ^ alpha ≠ 1 := by
    intro he
    apply ht1
    exact (Real.rpow_left_inj ht.le zero_le_one ha).mp (by simpa using he)
  have he : (2 + 2 / alpha - 2) / 2 = 1 / alpha := by ring
  have he' : 1 / (1 / alpha) = alpha := by field_simp [ha]
  have hroot : (t ^ alpha) ^ (1 / alpha) = t := by
    rw [← Real.rpow_mul ht.le, show alpha * (1 / alpha) = 1 by field_simp [ha], Real.rpow_one]
  unfold inverseGramQuadratic gramCoordinates
  rw [hA, hB, hC, he, he', ← twoSpectralMatrix_spectral,
    twoSpectralMatrix_power htalpha hq, hroot]

end

end ResearchMain.DiagonalSchatten
