import MainTheorems.DiagonalSchatten.ChartHessianKernel

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise Topology

def matrixFromCoordinates (v : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![v 0, v 1; v 2, v 3]

theorem matrixCoordinates_matrixFromCoordinates (v : Fin 4 → ℝ) :
    matrixCoordinates (matrixFromCoordinates v) = v := by
  ext j
  fin_cases j <;> simp [matrixCoordinates, matrixFromCoordinates]

def chartCoreDirection (h t w : ℝ) (i : Fin 3) : Fin 4 → ℝ :=
  ![spectralChartTangentH t w, spectralChartTangentT w h, spectralChartTangentW t h] i

def chartPowerDirection (p h t w : ℝ) (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℝ :=
  matrixFromCoordinates fun j =>
    p * spectralChartEntries t w h j ^ (p - 1) * chartCoreDirection h t w i j

theorem spectralChartEntries_deriv_row (h t w : ℝ) (i : Fin 3) (j : Fin 4) :
    HasDerivAt (fun y => spectralChartEntries
        (chartVariation h t w i y 1) (chartVariation h t w i y 2)
        (chartVariation h t w i y 0) j)
      (chartCoreDirection h t w i j) (chartBaseParameter h t w i) := by
  fin_cases i
  · simpa [chartVariation, chartBaseParameter, chartCoreDirection] using
      spectralChartEntries_deriv_h h t w j
  · simpa [chartVariation, chartBaseParameter, chartCoreDirection] using
      spectralChartEntries_deriv_t h t w j
  · simpa [chartVariation, chartBaseParameter, chartCoreDirection] using
      spectralChartEntries_deriv_w h t w j

theorem rationalSVDPowers_deriv_row (p h t w : ℝ) (i : Fin 3)
    (hM : ∀ a b, 0 < rationalSVDCore t w h a b) :
    HasDerivAt (fun y => rationalSVDPowers p
        (chartVariation h t w i y 0) (chartVariation h t w i y 1)
        (chartVariation h t w i y 2))
      (chartPowerDirection p h t w i) (chartBaseParameter h t w i) := by
  have hpos (j : Fin 4) : 0 < spectralChartEntries t w h j := by
    fin_cases j
    · simpa [spectralChartEntries, rationalSVDCore] using hM 0 0
    · simpa [spectralChartEntries, rationalSVDCore] using hM 0 1
    · simpa [spectralChartEntries, rationalSVDCore] using hM 1 0
    · simpa [spectralChartEntries, rationalSVDCore] using hM 1 1
  have hd (j : Fin 4) := (spectralChartEntries_deriv_row h t w i j).rpow_const
    (p := p) (Or.inl (by
      rw [chartVariation_at_base]
      exact (hpos j).ne'))
  apply hasDerivAt_pi.mpr
  intro a
  apply hasDerivAt_pi.mpr
  intro b
  fin_cases a <;> fin_cases b
  · convert! hd 0 using 1
    simp [spectralChartEntries, chartPowerDirection, matrixFromCoordinates, chartVariation_at_base]
    ring
  · convert! hd 1 using 1
    simp [spectralChartEntries, chartPowerDirection, matrixFromCoordinates, chartVariation_at_base]
    ring
  · convert! hd 2 using 1
    simp [spectralChartEntries, chartPowerDirection, matrixFromCoordinates, chartVariation_at_base]
    ring
  · convert! hd 3 using 1
    simp [spectralChartEntries, chartPowerDirection, matrixFromCoordinates, chartVariation_at_base]
    ring

theorem compressionHessian_deriv_curve {p : ℝ} (hp : 0 < p)
    (B E : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2)
    (c : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ)
    (V : Matrix (Fin 2) (Fin 2) ℝ) (hc : HasDerivAt c V x) (he : c x = B) :
    HasDerivAt (fun y => fderiv ℝ (compressionFunctional p) (c y) E)
      (compressionHessian p B V E) x := by
  have h2 := contDiffAt_compressionFunctional_fullRank (n := 2) hp B hB hdet
  have hD : DifferentiableAt ℝ (fderiv ℝ (compressionFunctional p)) B :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hscalar := hD.hasFDerivAt.clm_apply (hasFDerivAt_const E B)
  have hvalue := hscalar.comp_hasDerivAt_of_eq x hc he.symm
  change HasDerivAt (fun y => fderiv ℝ (compressionFunctional p) (c y) E)
    (fderiv ℝ (compressionFunctional p) B 0 + compressionHessian p B V E) x at hvalue
  simpa only [ContinuousLinearMap.map_zero, zero_add] using hvalue

theorem chart_compressionHessian_value {p h t w : ℝ} (hp : 0 < p)
    (hh : 0 < h) (hh1 : h < 1) (hM : ∀ a b, 0 < rationalSVDCore t w h a b)
    (i : Fin 3) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    chartDerivativeScale h t w i *
        compressionHessian p (rationalSVDPowers p h t w)
          (chartPowerDirection p h t w i) E =
      spectralChartScale p t w *
        ∑ j, normalizedSpectralJacobian p (h ^ (p - 1)) h t w i j *
          (matrixCoordinates E j / spectralChartEntries t w h j ^ p) := by
  let c : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun y =>
    rationalSVDPowers p (chartVariation h t w i y 0)
      (chartVariation h t w i y 1) (chartVariation h t w i y 2)
  let x := chartBaseParameter h t w i
  have hbase : (![h, t, w] : Fin 3 → ℝ) ∈ rationalSVDDomain := ⟨hh, hh1, hM⟩
  have hvar := (contDiff_chartVariation (n := 1) h t w i).continuous.continuousAt (x := x)
  have hlocal : ∀ᶠ y in 𝓝 x, chartVariation h t w i y ∈ rationalSVDDomain := by
    apply hvar.eventually
    rw [show x = chartBaseParameter h t w i by rfl, chartVariation_at_base]
    exact rationalSVDDomain_open.mem_nhds hbase
  have he : c x = rationalSVDPowers p h t w := by
    dsimp [c, x]
    rw [chartVariation_at_base]
    rfl
  have hroot : realEntryRoot p (rationalSVDPowers p h t w) = rationalSVDCore t w h :=
    realEntryRoot_realEntryPowers hp.ne' (rationalSVDCore t w h)
    (fun a b => (hM a b).le)
  have hdet : 0 < gramFirst (realEntryRoot p (rationalSVDPowers p h t w)) *
      gramSecond (realEntryRoot p (rationalSVDPowers p h t w)) -
        gramCross (realEntryRoot p (rationalSVDPowers p h t w)) ^ 2 := by
    rw [hroot, rationalSVDCore_gramDet]
    positivity
  have hactual := compressionHessian_deriv_curve hp _ E
    (rationalSVDPowers_positive hM) hdet c x (chartPowerDirection p h t w i)
    (rationalSVDPowers_deriv_row p h t w i hM) he
  have hpos (j : Fin 4) : 0 < spectralChartEntries t w h j := by
    fin_cases j
    · simpa [spectralChartEntries, rationalSVDCore] using hM 0 0
    · simpa [spectralChartEntries, rationalSVDCore] using hM 0 1
    · simpa [spectralChartEntries, rationalSVDCore] using hM 1 0
    · simpa [spectralChartEntries, rationalSVDCore] using hM 1 1
  choose v hd hv using fun j => spectralChartGradient_deriv_row p t w hh i j (hpos j)
  have hsum : HasDerivAt (fun y =>
      ∑ j, spectralChartGradient p (chartVariation h t w i y 0)
        (chartVariation h t w i y 1) (chartVariation h t w i y 2) j * matrixCoordinates E j)
      (∑ j, v j * matrixCoordinates E j) x :=
    HasDerivAt.fun_sum fun j _ => (hd j).mul_const (matrixCoordinates E j)
  have heq : (fun y =>
      ∑ j, spectralChartGradient p (chartVariation h t w i y 0)
        (chartVariation h t w i y 1) (chartVariation h t w i y 2) j * matrixCoordinates E j) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (compressionFunctional p) (c y) E) := by
    filter_upwards [hlocal] with y hy
    exact (fderiv_compressionFunctional_chart_coordinates hp hy.1 hy.2.1 hy.2.2 E).symm
  have hvalue := hsum.unique (hactual.congr_of_eventuallyEq heq)
  rw [← hvalue, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hden := (Real.rpow_pos_of_pos (hpos j) p).ne'
  calc
    chartDerivativeScale h t w i * (v j * matrixCoordinates E j) =
        (chartDerivativeScale h t w i * v j * spectralChartEntries t w h j ^ p) *
          matrixCoordinates E j / spectralChartEntries t w h j ^ p := by
      field_simp [hden]
    _ = _ := by rw [hv j]; ring

end

end ResearchMain.DiagonalSchatten
