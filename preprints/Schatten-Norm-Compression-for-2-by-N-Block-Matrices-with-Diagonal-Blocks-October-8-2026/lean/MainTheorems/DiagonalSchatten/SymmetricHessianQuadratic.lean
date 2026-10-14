import MainTheorems.DiagonalSchatten.SymmetricHessianValues

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

def symmetricRadialDifference (p h : ℝ) (E : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (E 0 0 + E 1 1) / (1 + h) ^ p - (E 0 1 + E 1 0) / (1 - h) ^ p

theorem symmetric_compressionHessian_h {p h : ℝ} (hp : 0 < p)
    (hh : 0 < h) (hh1 : h < 1) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    compressionHessian p (rationalSVDPowers p h 1 1) (chartPowerDirection p h 1 1 0) E =
      spectralChartScale p 1 1 * (p - 1) * (h ^ (p - 1) - h) / h *
        symmetricRadialDifference p h E := by
  have he := chart_compressionHessian_value hp hh hh1 (symmetric_core_positive hh hh1) 0 E
  rw [normalizedSpectralJacobian_first_row] at he
  simp [Fin.sum_univ_succ, chartDerivativeScale, matrixCoordinates, spectralChartEntries,
    symmetricRadialDifference] at he ⊢
  field_simp [hh.ne'] at he ⊢
  linear_combination he

theorem symmetric_matrix_decomposition {p h : ℝ} (hp : 0 < p)
    (hh : 0 < h) (hh1 : h < 1) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    E =
      (((E 0 0 + E 1 1) / (1 + h) ^ (p - 1) +
        (E 0 1 + E 1 0) / (1 - h) ^ (p - 1)) / 4) • rationalSVDPowers p h 1 1 +
      (symmetricRadialDifference p h E * (1 + h) * (1 - h) / (4 * p)) •
        chartPowerDirection p h 1 1 0 +
      ((E 0 0 - E 1 1) / 2) • diagonalDifference +
      ((E 0 1 - E 1 0) / 2) • offDiagonalDifference := by
  have hU : 0 < 1 + h := by positivity
  have hV : 0 < 1 - h := by linarith
  have hUp : (1 + h) ^ p = (1 + h) ^ (p - 1) * (1 + h) := by
    calc
      (1 + h) ^ p = (1 + h) ^ ((p - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hU, Real.rpow_one]
  have hVp : (1 - h) ^ p = (1 - h) ^ (p - 1) * (1 - h) := by
    calc
      (1 - h) ^ p = (1 - h) ^ ((p - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hV, Real.rpow_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalSVDPowers, realEntryPowers, rationalSVDCore, chartPowerDirection,
      matrixFromCoordinates, chartCoreDirection, spectralChartEntries, spectralChartTangentH,
      diagonalDifference, offDiagonalDifference, symmetricRadialDifference, hUp, hVp]
  all_goals
    field_simp [hp.ne', hU.ne', hV.ne', (Real.rpow_pos_of_pos hU (p - 1)).ne',
      (Real.rpow_pos_of_pos hV (p - 1)).ne']
    ring

theorem symmetric_compressionHessian_quadratic {p h : ℝ} (hp : 1 < p)
    (hh : 0 < h) (hh1 : h < 1) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    compressionHessian p (rationalSVDPowers p h 1 1) E E =
      (spectralChartScale p 1 1 * (p - 1) * (h ^ (p - 1) - h) / h *
        ((1 + h) * (1 - h) / (4 * p))) * symmetricRadialDifference p h E ^ 2 +
      (spectralChartScale p 1 1 * symmetricDiagonalBracket (p - 1) h /
        (2 * p * (1 - h) * (1 + h) ^ (p - 1) * (1 + h) ^ p)) * (E 0 0 - E 1 1) ^ 2 +
      (spectralChartScale p 1 1 * symmetricOffDiagonalBracket (p - 1) h /
        (2 * p * (1 + h) * (1 - h) ^ (p - 1) * (1 - h) ^ p)) * (E 0 1 - E 1 0) ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hM := symmetric_core_positive hh hh1
  have hroot : realEntryRoot p (rationalSVDPowers p h 1 1) = rationalSVDCore 1 1 h :=
    realEntryRoot_realEntryPowers hp0.ne' _ (fun i j => (hM i j).le)
  have hdet : 0 < gramFirst (realEntryRoot p (rationalSVDPowers p h 1 1)) *
      gramSecond (realEntryRoot p (rationalSVDPowers p h 1 1)) -
        gramCross (realEntryRoot p (rationalSVDPowers p h 1 1)) ^ 2 := by
    rw [hroot, rationalSVDCore_gramDet]
    positivity
  have hrad := compressionHessian_radial_zero hp _ (rationalSVDPowers_positive hM) hdet
  have he := congrArg (fun V => compressionHessian p (rationalSVDPowers p h 1 1) V E)
    (symmetric_matrix_decomposition hp0 hh hh1 E)
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hrad, zero_apply, mul_zero,
    zero_add] at he
  rw [symmetric_compressionHessian_h hp0 hh hh1 E,
    symmetric_compressionHessian_diagonal hp hh hh1 E,
    symmetric_compressionHessian_offDiagonal hp0 hh hh1 E] at he
  rw [he]
  have hU : 0 < 1 + h := by positivity
  have hV : 0 < 1 - h := by linarith
  field_simp [hp0.ne', hh.ne', hU.ne', hV.ne',
    (Real.rpow_pos_of_pos hU (p - 1)).ne', (Real.rpow_pos_of_pos hV (p - 1)).ne',
    (Real.rpow_pos_of_pos hU p).ne', (Real.rpow_pos_of_pos hV p).ne']

theorem symmetric_compressionHessian_nonneg {p h : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hh : 0 < h) (hh1 : h < 1) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    0 ≤ compressionHessian p (rationalSVDPowers p h 1 1) E E := by
  rw [symmetric_compressionHessian_quadratic hp hh hh1 E]
  have hq : 0 < p - 1 := by linarith
  have hq1 : p - 1 < 1 := by linarith
  have hpow : h < h ^ (p - 1) := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_gt hh hh1 hq1
  have hd := symmetricDiagonalBracket_positive hq hq1 hh hh1
  have ho := symmetricOffDiagonalBracket_positive hq hq1 hh hh1
  have hV : 0 < 1 - h := by linarith
  have hs : 0 < spectralChartScale p 1 1 := Real.rpow_pos_of_pos (by positivity) _
  positivity

theorem symmetric_compressionHessian_nonpos {p h : ℝ} (hp : 2 < p)
    (hh : 0 < h) (hh1 : h < 1) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    compressionHessian p (rationalSVDPowers p h 1 1) E E ≤ 0 := by
  have hp1 : 1 < p := by linarith
  rw [symmetric_compressionHessian_quadratic hp1 hh hh1 E]
  have hq : 1 < p - 1 := by linarith
  have hpow : h ^ (p - 1) < h := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_gt hh hh1 hq
  have hd := symmetricDiagonalBracket_negative hq hh hh1
  have ho := symmetricOffDiagonalBracket_negative hq hh hh1
  have hV : 0 < 1 - h := by linarith
  have hs : 0 < spectralChartScale p 1 1 := Real.rpow_pos_of_pos (by positivity) _
  have hp0 : 0 < p := by linarith
  apply add_nonpos
  · apply add_nonpos
    · exact mul_nonpos_of_nonpos_of_nonneg (by
        apply mul_nonpos_of_nonpos_of_nonneg
        · exact div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hpow.le)) hh.le
        · positivity) (sq_nonneg _)
    · exact mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hs.le hd.le)
          (by positivity)) (sq_nonneg _)
  · exact mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hs.le ho.le)
        (by positivity)) (sq_nonneg _)

end

end ResearchMain.DiagonalSchatten
