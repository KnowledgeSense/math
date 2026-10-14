import MainTheorems.DiagonalSchatten.ChartHessianValues
import MainTheorems.DiagonalSchatten.TanhPowerSigns

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

def diagonalDifference : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

def offDiagonalDifference : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

theorem symmetric_core_positive {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    ∀ i j, 0 < rationalSVDCore 1 1 h i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [rationalSVDCore] <;> linarith

theorem symmetric_power_direction_difference (p h : ℝ) :
    chartPowerDirection p h 1 1 1 - chartPowerDirection p h 1 1 2 =
      (p * (1 + h) * (1 - h) ^ (p - 1)) • offDiagonalDifference := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartPowerDirection, chartCoreDirection, matrixFromCoordinates,
      spectralChartEntries, spectralChartTangentT, spectralChartTangentW,
      offDiagonalDifference] <;> ring

theorem symmetric_power_direction_sum (p : ℝ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    chartPowerDirection p h 1 1 1 + chartPowerDirection p h 1 1 2 -
        p • rationalSVDPowers p h 1 1 =
      (-(p * (1 - h) * (1 + h) ^ (p - 1))) • diagonalDifference := by
  have hUp : (1 + h) ^ p = (1 + h) ^ (p - 1) * (1 + h) := by
    calc
      (1 + h) ^ p = (1 + h) ^ ((p - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add (by positivity), Real.rpow_one]
  have hVp : (1 - h) ^ p = (1 - h) ^ (p - 1) * (1 - h) := by
    calc
      (1 - h) ^ p = (1 - h) ^ ((p - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add (by linarith), Real.rpow_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartPowerDirection, chartCoreDirection, matrixFromCoordinates,
      spectralChartEntries, spectralChartTangentT, spectralChartTangentW,
      rationalSVDPowers, realEntryPowers, rationalSVDCore, diagonalDifference,
      hUp, hVp] <;> ring

theorem symmetric_jacobian_sum {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (p : ℝ) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    (∑ j, (normalizedSpectralJacobian p (h ^ (p - 1)) h 1 1 1 j +
        normalizedSpectralJacobian p (h ^ (p - 1)) h 1 1 2 j) *
        (matrixCoordinates E j / spectralChartEntries 1 1 h j ^ p)) =
      -2 * symmetricDiagonalBracket (p - 1) h * (E 0 0 - E 1 1) / (1 + h) ^ p := by
  have hU : (1 + h) ^ p ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hV : (1 - h) ^ p ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  simp [Fin.sum_univ_succ, normalizedSpectralJacobian, spectralChartEntries,
    spectralChartTangentT, spectralChartTangentW, matrixCoordinates,
    symmetricDiagonalBracket]
  field_simp [hU, hV]
  ring

theorem symmetric_jacobian_difference {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (p : ℝ) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    (∑ j, (normalizedSpectralJacobian p (h ^ (p - 1)) h 1 1 1 j -
        normalizedSpectralJacobian p (h ^ (p - 1)) h 1 1 2 j) *
        (matrixCoordinates E j / spectralChartEntries 1 1 h j ^ p)) =
      2 * symmetricOffDiagonalBracket (p - 1) h * (E 0 1 - E 1 0) / (1 - h) ^ p := by
  have hU : (1 + h) ^ p ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hV : (1 - h) ^ p ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  simp [Fin.sum_univ_succ, normalizedSpectralJacobian, spectralChartEntries,
    spectralChartTangentT, spectralChartTangentW, matrixCoordinates,
    symmetricOffDiagonalBracket]
  field_simp [hU, hV]
  ring

theorem symmetric_compressionHessian_diagonal {p h : ℝ} (hp : 1 < p)
    (hh : 0 < h) (hh1 : h < 1) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    compressionHessian p (rationalSVDPowers p h 1 1) diagonalDifference E =
      spectralChartScale p 1 1 * symmetricDiagonalBracket (p - 1) h /
        (p * (1 - h) * (1 + h) ^ (p - 1) * (1 + h) ^ p) * (E 0 0 - E 1 1) := by
  have hM := symmetric_core_positive hh hh1
  have hp0 : 0 < p := by linarith
  have ht := chart_compressionHessian_value hp0 hh hh1 hM 1 E
  have hw := chart_compressionHessian_value hp0 hh hh1 hM 2 E
  norm_num [chartDerivativeScale] at ht hw
  have hsum : 2 * (compressionHessian p (rationalSVDPowers p h 1 1)
        (chartPowerDirection p h 1 1 1) E +
      compressionHessian p (rationalSVDPowers p h 1 1)
        (chartPowerDirection p h 1 1 2) E) =
      spectralChartScale p 1 1 *
        (-2 * symmetricDiagonalBracket (p - 1) h * (E 0 0 - E 1 1) / (1 + h) ^ p) := by
    rw [← symmetric_jacobian_sum hh hh1 p E]
    simp only [add_mul, Finset.sum_add_distrib]
    nlinarith [ht, hw]
  have hroot : realEntryRoot p (rationalSVDPowers p h 1 1) = rationalSVDCore 1 1 h :=
    realEntryRoot_realEntryPowers hp0.ne' _ (fun i j => (hM i j).le)
  have hdet : 0 < gramFirst (realEntryRoot p (rationalSVDPowers p h 1 1)) *
      gramSecond (realEntryRoot p (rationalSVDPowers p h 1 1)) -
        gramCross (realEntryRoot p (rationalSVDPowers p h 1 1)) ^ 2 := by
    rw [hroot, rationalSVDCore_gramDet]
    positivity
  have hrad := compressionHessian_radial_zero hp _ (rationalSVDPowers_positive hM) hdet
  have hid := congrArg (fun V => compressionHessian p (rationalSVDPowers p h 1 1) V E)
    (symmetric_power_direction_sum p hh hh1)
  simp only [map_sub, map_add, map_smul, add_apply, sub_apply, smul_apply, smul_eq_mul, hrad,
    zero_apply, mul_zero, sub_zero] at hid
  rw [hid] at hsum
  have hV : 0 < 1 - h := by linarith
  have hden : p * (1 - h) * (1 + h) ^ (p - 1) * (1 + h) ^ p ≠ 0 := by positivity
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hden).mpr
  field_simp [(Real.rpow_pos_of_pos (show 0 < 1 + h by positivity) p).ne'] at hsum ⊢
  nlinarith [hsum]

theorem symmetric_compressionHessian_offDiagonal {p h : ℝ} (hp : 0 < p)
    (hh : 0 < h) (hh1 : h < 1) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    compressionHessian p (rationalSVDPowers p h 1 1) offDiagonalDifference E =
      spectralChartScale p 1 1 * symmetricOffDiagonalBracket (p - 1) h /
        (p * (1 + h) * (1 - h) ^ (p - 1) * (1 - h) ^ p) * (E 0 1 - E 1 0) := by
  have hM := symmetric_core_positive hh hh1
  have ht := chart_compressionHessian_value hp hh hh1 hM 1 E
  have hw := chart_compressionHessian_value hp hh hh1 hM 2 E
  norm_num [chartDerivativeScale] at ht hw
  have hdiff : 2 * (compressionHessian p (rationalSVDPowers p h 1 1)
        (chartPowerDirection p h 1 1 1) E -
      compressionHessian p (rationalSVDPowers p h 1 1)
        (chartPowerDirection p h 1 1 2) E) =
      spectralChartScale p 1 1 *
        (2 * symmetricOffDiagonalBracket (p - 1) h * (E 0 1 - E 1 0) / (1 - h) ^ p) := by
    rw [← symmetric_jacobian_difference hh hh1 p E]
    simp only [sub_mul, Finset.sum_sub_distrib]
    nlinarith [ht, hw]
  have hid := congrArg (fun V => compressionHessian p (rationalSVDPowers p h 1 1) V E)
    (symmetric_power_direction_difference p h)
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul] at hid
  rw [hid] at hdiff
  have hV : 0 < 1 - h := by linarith
  have hden : p * (1 + h) * (1 - h) ^ (p - 1) * (1 - h) ^ p ≠ 0 := by positivity
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hden).mpr
  field_simp [(Real.rpow_pos_of_pos (show 0 < 1 - h by linarith) p).ne'] at hdiff ⊢
  nlinarith [hdiff]

end

end ResearchMain.DiagonalSchatten
