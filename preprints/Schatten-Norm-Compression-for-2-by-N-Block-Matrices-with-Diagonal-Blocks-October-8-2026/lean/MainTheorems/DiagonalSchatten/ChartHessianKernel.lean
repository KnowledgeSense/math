import MainTheorems.DiagonalSchatten.ChartHessianConnection
import MainTheorems.DiagonalSchatten.SpectralJacobianKernel

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

def chartDerivativeScale (h t w : ℝ) : Fin 3 → ℝ := ![h, 1 + t ^ 2, 1 + w ^ 2]

theorem spectralChartGradient_deriv_row (p t w : ℝ) {h : ℝ} (hh : 0 < h)
    (i : Fin 3) (j : Fin 4) (hpos : 0 < spectralChartEntries t w h j) :
    ∃ v, HasDerivAt (fun y => spectralChartGradient p (chartVariation h t w i y 0)
        (chartVariation h t w i y 1) (chartVariation h t w i y 2) j)
      v (chartBaseParameter h t w i) ∧
      chartDerivativeScale h t w i * v * spectralChartEntries t w h j ^ p =
        spectralChartScale p t w * normalizedSpectralJacobian p (h ^ (p - 1)) h t w i j := by
  fin_cases i
  · simpa [chartVariation, chartBaseParameter, chartDerivativeScale] using
      spectralChartGradient_deriv_h p t w hh j hpos
  · simpa [chartVariation, chartBaseParameter, chartDerivativeScale] using
      spectralChartGradient_deriv_t p h t w j hpos
  · simpa [chartVariation, chartBaseParameter, chartDerivativeScale] using
      spectralChartGradient_deriv_w p h t w j hpos

theorem normalized_derivative_sum_zero {J : Type*} [Fintype J]
    (r s : ℝ) (v D M E : J → ℝ) (hs : s ≠ 0) (hD : ∀ j, D j ≠ 0)
    (hN : ∀ j, r * v j * D j = s * M j) (hv : ∑ j, v j * E j = 0) :
    ∑ j, M j * (E j / D j) = 0 := by
  have he : s * (∑ j, M j * (E j / D j)) = r * (∑ j, v j * E j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      s * (M j * (E j / D j)) = (s * M j) * E j / D j := by ring
      _ = (r * v j * D j) * E j / D j := by rw [hN j]
      _ = r * (v j * E j) := by field_simp [hD j]
  rw [hv, mul_zero] at he
  exact (mul_eq_zero.mp he).resolve_left hs

theorem chart_hessian_kernel_jacobian {p h t w : ℝ} (hp : 0 < p)
    (hh : 0 < h) (hh1 : h < 1) (hM : ∀ i j, 0 < rationalSVDCore t w h i j)
    (E : Matrix (Fin 2) (Fin 2) ℝ)
    (hE : compressionHessian p (rationalSVDPowers p h t w) E = 0) :
    (normalizedSpectralJacobian p (h ^ (p - 1)) h t w).mulVec
      (fun j => matrixCoordinates E j / spectralChartEntries t w h j ^ p) = 0 := by
  classical
  have hpos (j : Fin 4) : 0 < spectralChartEntries t w h j := by
    fin_cases j
    · simpa [spectralChartEntries, rationalSVDCore] using hM 0 0
    · simpa [spectralChartEntries, rationalSVDCore] using hM 0 1
    · simpa [spectralChartEntries, rationalSVDCore] using hM 1 0
    · simpa [spectralChartEntries, rationalSVDCore] using hM 1 1
  have hs : spectralChartScale p t w ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity) _).ne'
  funext i
  choose v hd hv using fun j => spectralChartGradient_deriv_row p t w hh i j (hpos j)
  have hsum : HasDerivAt (fun y =>
      ∑ j, spectralChartGradient p (chartVariation h t w i y 0)
        (chartVariation h t w i y 1) (chartVariation h t w i y 2) j * matrixCoordinates E j)
      (∑ j, v j * matrixCoordinates E j) (chartBaseParameter h t w i) := by
    exact HasDerivAt.fun_sum fun j _ => (hd j).mul_const (matrixCoordinates E j)
  have hz := hsum.unique (chart_hessian_kernel_gradient_curve hp hh hh1 hM E hE i)
  exact normalized_derivative_sum_zero (chartDerivativeScale h t w i) (spectralChartScale p t w)
    v (fun j => spectralChartEntries t w h j ^ p)
    (fun j => normalizedSpectralJacobian p (h ^ (p - 1)) h t w i j)
    (matrixCoordinates E) hs (fun j => (Real.rpow_pos_of_pos (hpos j) _).ne') hv hz

theorem chart_compressionHessian_kernel_radial {p h t w : ℝ}
    (hp : 1 < p) (hp2 : p ≠ 2) (hh : 0 < h) (hh1 : h < 1)
    (ht : 0 < t) (hw : 0 < w) (hM : ∀ i j, 0 < rationalSVDCore t w h i j)
    (E : Matrix (Fin 2) (Fin 2) ℝ)
    (hE : compressionHessian p (rationalSVDPowers p h t w) E = 0) :
    ∃ r : ℝ, E = r • rationalSVDPowers p h t w := by
  let z : Fin 4 → ℝ := fun j => matrixCoordinates E j / spectralChartEntries t w h j ^ p
  have hJ := chart_hessian_kernel_jacobian (by linarith : 0 < p) hh hh1 hM E hE
  have hconst := normalizedSpectralJacobian_kernel hp hp2 hh hh1 ht hw z hJ
  refine ⟨z 3, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · have he := hconst 0
    change E 0 0 / rationalSVDCore t w h 0 0 ^ p = z 3 at he
    exact (div_eq_iff (Real.rpow_pos_of_pos (hM 0 0) p).ne').mp he
  · have he := hconst 1
    change E 0 1 / rationalSVDCore t w h 0 1 ^ p = z 3 at he
    exact (div_eq_iff (Real.rpow_pos_of_pos (hM 0 1) p).ne').mp he
  · have he := hconst 2
    change E 1 0 / rationalSVDCore t w h 1 0 ^ p = z 3 at he
    exact (div_eq_iff (Real.rpow_pos_of_pos (hM 1 0) p).ne').mp he
  · change E 1 1 = (E 1 1 / rationalSVDCore t w h 1 1 ^ p) * rationalSVDCore t w h 1 1 ^ p
    field_simp [(Real.rpow_pos_of_pos (hM 1 1) p).ne']

end

end ResearchMain.DiagonalSchatten
