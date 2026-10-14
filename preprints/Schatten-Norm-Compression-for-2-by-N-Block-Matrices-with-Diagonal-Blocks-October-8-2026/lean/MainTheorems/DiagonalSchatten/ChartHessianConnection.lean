import MainTheorems.DiagonalSchatten.RationalSVDGradient
import MainTheorems.DiagonalSchatten.CompressionHessian
import MainTheorems.DiagonalSchatten.SpectralChartDerivatives
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise Topology

def matrixCoordinates (E : Matrix (Fin 2) (Fin 2) ℝ) : Fin 4 → ℝ :=
  ![E 0 0, E 0 1, E 1 0, E 1 1]

def chartVariation (h t w : ℝ) (i : Fin 3) (x : ℝ) : Fin 3 → ℝ :=
  ![if i = 0 then x else h, if i = 1 then x else t, if i = 2 then x else w]

def chartBaseParameter (h t w : ℝ) : Fin 3 → ℝ := ![h, t, w]

theorem chartVariation_at_base (h t w : ℝ) (i : Fin 3) :
    chartVariation h t w i (chartBaseParameter h t w i) = ![h, t, w] := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [chartVariation, chartBaseParameter]

theorem contDiff_chartVariation {n : WithTop ℕ∞} (h t w : ℝ) (i : Fin 3) :
    ContDiff ℝ n (chartVariation h t w i) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp [chartVariation] <;> fun_prop

def rationalSVDDomain : Set (Fin 3 → ℝ) :=
  {x | 0 < x 0 ∧ x 0 < 1 ∧ ∀ i j, 0 < rationalSVDCore (x 1) (x 2) (x 0) i j}

theorem rationalSVDDomain_open : IsOpen rationalSVDDomain := by
  have hc : IsOpen {x : Fin 3 → ℝ | ∀ i j, 0 < rationalSVDCore (x 1) (x 2) (x 0) i j} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_lt continuous_const
    fin_cases i <;> fin_cases j <;> simp [rationalSVDCore] <;> fun_prop
  simpa only [rationalSVDDomain, Set.ofPred_and] using
    (isOpen_lt continuous_const (show Continuous (fun x : Fin 3 → ℝ => x 0) by fun_prop)).inter
      ((isOpen_lt (show Continuous (fun x : Fin 3 → ℝ => x 0) by fun_prop) continuous_const).inter hc)

theorem contDiffAt_rationalSVDPowers {n : WithTop ℕ∞} (p : ℝ) (x : Fin 3 → ℝ)
    (hx : ∀ i j, 0 < rationalSVDCore (x 1) (x 2) (x 0) i j) :
    ContDiffAt ℝ n (fun y : Fin 3 → ℝ => rationalSVDPowers p (y 0) (y 1) (y 2)) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hc : ContDiffAt ℝ n (fun y : Fin 3 → ℝ => rationalSVDCore (y 1) (y 2) (y 0) i j) x := by
    fin_cases i <;> fin_cases j <;> simp [rationalSVDCore] <;> fun_prop
  exact hc.rpow_const_of_ne (hx i j).ne'

theorem fderiv_compressionFunctional_chart_coordinates {p h t w : ℝ} (hp : 0 < p)
    (hh : 0 < h) (hh1 : h < 1) (hM : ∀ i j, 0 < rationalSVDCore t w h i j)
    (E : Matrix (Fin 2) (Fin 2) ℝ) :
    fderiv ℝ (compressionFunctional p) (rationalSVDPowers p h t w) E =
      ∑ j, spectralChartGradient p h t w j * matrixCoordinates E j := by
  rw [fderiv_compressionFunctional_rationalSVD hp hh hh1 hM E]
  simp [Fin.sum_univ_two, Fin.sum_univ_four, rationalSVDGradient,
    spectralChartGradient, spectralChartScale, spectralChartEntries,
    rationalSVDCore, matrixCoordinates]
  ring

theorem compressionHessian_kernel_deriv_curve {p : ℝ} (hp : 0 < p)
    (B E : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2)
    (hE : compressionHessian p B E = 0) (c : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (x : ℝ) (hc : DifferentiableAt ℝ c x) (he : c x = B) :
    HasDerivAt (fun y => fderiv ℝ (compressionFunctional p) (c y) E) 0 x := by
  have h2 := contDiffAt_compressionFunctional_fullRank (n := 2) hp B hB hdet
  have hD : DifferentiableAt ℝ (fderiv ℝ (compressionFunctional p)) B :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hscalar := hD.hasFDerivAt.clm_apply (hasFDerivAt_const E B)
  have hvalue := hscalar.comp_hasDerivAt_of_eq x hc.hasDerivAt he.symm
  change HasDerivAt (fun y => fderiv ℝ (compressionFunctional p) (c y) E)
    (fderiv ℝ (compressionFunctional p) B 0 + compressionHessian p B (deriv c x) E) x at hvalue
  have hz : compressionHessian p B (deriv c x) E = 0 := by
    rw [compressionHessian_symmetric hp B hB hdet, hE]
    rfl
  simpa only [ContinuousLinearMap.map_zero, zero_add, hz] using hvalue

theorem chart_hessian_kernel_gradient_curve {p h t w : ℝ} (hp : 0 < p)
    (hh : 0 < h) (hh1 : h < 1) (hM : ∀ i j, 0 < rationalSVDCore t w h i j)
    (E : Matrix (Fin 2) (Fin 2) ℝ)
    (hE : compressionHessian p (rationalSVDPowers p h t w) E = 0) (i : Fin 3) :
    HasDerivAt (fun y =>
      ∑ j, spectralChartGradient p (chartVariation h t w i y 0)
        (chartVariation h t w i y 1) (chartVariation h t w i y 2) j * matrixCoordinates E j)
      0 (chartBaseParameter h t w i) := by
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
  have hdiff : DifferentiableAt ℝ c x := by
    have hpowers : ContDiffAt ℝ 1
        (fun y : Fin 3 → ℝ => rationalSVDPowers p (y 0) (y 1) (y 2))
        (chartVariation h t w i x) := by
      rw [show x = chartBaseParameter h t w i by rfl, chartVariation_at_base]
      exact contDiffAt_rationalSVDPowers p ![h, t, w] hM
    exact (hpowers.comp x (contDiff_chartVariation (n := 1) h t w i).contDiffAt).differentiableAt
      (by norm_num)
  have he : c x = rationalSVDPowers p h t w := by
    dsimp [c, x]
    rw [chartVariation_at_base]
    rfl
  have hroot : realEntryRoot p (rationalSVDPowers p h t w) = rationalSVDCore t w h :=
    realEntryRoot_realEntryPowers hp.ne' _ (fun a b => (hM a b).le)
  have hdet : 0 < gramFirst (realEntryRoot p (rationalSVDPowers p h t w)) *
      gramSecond (realEntryRoot p (rationalSVDPowers p h t w)) -
        gramCross (realEntryRoot p (rationalSVDPowers p h t w)) ^ 2 := by
    rw [hroot, rationalSVDCore_gramDet]
    positivity
  have hd := compressionHessian_kernel_deriv_curve hp _ E (rationalSVDPowers_positive hM)
    hdet hE c x hdiff he
  apply hd.congr_of_eventuallyEq
  filter_upwards [hlocal] with y hy
  exact (fderiv_compressionFunctional_chart_coordinates hp hy.1 hy.2.1 hy.2.2 E).symm

end

end ResearchMain.DiagonalSchatten
