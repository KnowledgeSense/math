import AperyMoments.CauchyRemainder

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

def outsideDensity (h : ℝ → ℝ) (a r : ℝ) : ℝ → ℝ := (Icc (a - r) (a + r))ᶜ.indicator h

theorem densityCauchyTransform_indicator (h : ℝ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) (z : ℂ) :
    densityCauchyTransform (s.indicator h) z = ∫ t in s, densityCauchyKernel h z t := by
  unfold densityCauchyTransform
  have he : densityCauchyKernel (s.indicator h) z = s.indicator (densityCauchyKernel h z) := by
    funext t
    by_cases ht : t ∈ s <;> simp [densityCauchyKernel, ht]
  rw [he, integral_indicator hs]

theorem outsideDensity_measurable {h : ℝ → ℝ} (hh : Measurable h) (a r : ℝ) :
    Measurable (outsideDensity h a r) := hh.indicator measurableSet_Icc.compl

theorem outsideDensity_integrable {h : ℝ → ℝ} (hi : Integrable h) (a r : ℝ) :
    Integrable (outsideDensity h a r) := hi.indicator measurableSet_Icc.compl

theorem outsideDensity_separation (h : ℝ → ℝ) {a r : ℝ} (_hr : 0 < r) (t : ℝ)
    (ht : outsideDensity h a r t ≠ 0) : r ≤ ‖(a : ℂ) - t‖ := by
  have hout : t ∉ Icc (a - r) (a + r) := by
    intro hmem
    exact ht (indicator_of_notMem (by simpa using hmem) h)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  by_contra hh
  have habs := abs_lt.mp (lt_of_not_ge hh)
  exact hout ⟨by linarith, by linarith⟩

theorem outsideCauchy_continuousAt {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {a r : ℝ} (hr : 0 < r) :
    ContinuousAt (densityCauchyTransform (outsideDensity h a r)) (a : ℂ) :=
  (densityCauchyTransform_differentiableAt (outsideDensity_measurable hh a r)
    (outsideDensity_integrable hi a r) hr (outsideDensity_separation h hr)).continuousAt

theorem localCauchyRemainder_integrable {F : ℂ → ℂ} {a r : ℝ} (hr : 0 < r) {K : NNReal}
    (hF : LipschitzOnWith K F (closedBall (a : ℂ) (2 * r))) {z : ℂ} (hz : z.im ≠ 0) :
    IntervalIntegrable (fun t : ℝ => (F (t : ℂ) - F z) / (z - t)) volume (a - r) (a + r) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith : a - r ≤ a + r)]
  have hFr : ContinuousOn (fun t : ℝ => F (t : ℂ)) (Icc (a - r) (a + r)) := by
    apply hF.continuousOn.comp (by fun_prop)
    intro t ht
    exact (closedBall_subset_closedBall (by linarith : r ≤ 2 * r)) (real_interval_mem_closedBall hr.le ht)
  apply ContinuousOn.div (hFr.sub continuousOn_const) (by fun_prop)
  intro t _ he
  have h := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at h
  exact hz h

theorem constantCauchyKernel_integrable {z : ℂ} (hz : z.im ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => (z - t)⁻¹) volume a b := by
  apply Continuous.intervalIntegrable
  apply Continuous.inv₀ (by fun_prop)
  intro t ht
  have h := congrArg Complex.im ht
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at h
  exact hz h

theorem densityCauchy_local_decomposition {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {F : ℂ → ℂ} {a r : ℝ} (hr : 0 < r) {K : NNReal}
    (hF : LipschitzOnWith K F (closedBall (a : ℂ) (2 * r)))
    (heq : ∀ t ∈ Icc (a - r) (a + r), (h t : ℂ) = F (t : ℂ))
    {z : ℂ} (hz : z.im ≠ 0) :
    densityCauchyTransform h z = densityCauchyTransform (outsideDensity h a r) z +
      localCauchyRemainder F a r z + F z * ∫ t in (a - r)..(a + r), (z - t)⁻¹ := by
  have hiK := densityCauchyKernel_integrable hh hi (abs_pos.mpr hz) (fun t _ => cauchy_separation_nonreal hz t)
  have hs := integral_add_compl (s := Icc (a - r) (a + r)) measurableSet_Icc hiK
  have hout : densityCauchyTransform (outsideDensity h a r) z =
      ∫ t in (Icc (a - r) (a + r))ᶜ, densityCauchyKernel h z t :=
    densityCauchyTransform_indicator h measurableSet_Icc.compl z
  have hin : (∫ t in Icc (a - r) (a + r), densityCauchyKernel h z t) =
      localCauchyRemainder F a r z + F z * ∫ t in (a - r)..(a + r), (z - t)⁻¹ := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : a - r ≤ a + r)]
    unfold localCauchyRemainder
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (localCauchyRemainder_integrable hr hF hz)
      (IntervalIntegrable.const_mul (constantCauchyKernel_integrable hz _ _) (F z))]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith : a - r ≤ a + r)] at ht
    dsimp only
    unfold densityCauchyKernel
    rw [heq t ht]
    ring
  change _ = densityCauchyTransform h z at hs
  rw [hin, ← hout] at hs
  rw [← hs]
  ring

end AperyMoments
