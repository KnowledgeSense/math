import AperyMoments.CauchyPoisson
import AperyMoments.CauchyLocalDecomposition
import AperyMoments.CauchySymmetry

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

theorem densityCauchyTransform_real (h : ℝ → ℝ) (x : ℝ) :
    (densityCauchyTransform h (x : ℂ)).im = 0 := by
  have he := densityCauchyTransform_conj h (x : ℂ)
  rw [Complex.conj_ofReal] at he
  have hi := congrArg Complex.im he
  change (densityCauchyTransform h (x : ℂ)).im = -(densityCauchyTransform h (x : ℂ)).im at hi
  linarith

theorem densityCauchyTransform_split {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {s : Set ℝ} (hs : MeasurableSet s) {z : ℂ} (hz : z.im ≠ 0) :
    densityCauchyTransform h z = densityCauchyTransform (s.indicator h) z +
      densityCauchyTransform (sᶜ.indicator h) z := by
  rw [densityCauchyTransform_indicator h hs, densityCauchyTransform_indicator h hs.compl]
  exact (integral_add_compl hs (densityCauchyKernel_integrable hh hi (abs_pos.mpr hz)
    (fun t _ => cauchy_separation_nonreal hz t))).symm

/-- Only local continuity of the actual density is needed for the unrestricted imaginary boundary. -/
theorem densityCauchy_im_tendsto_upper {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {x : ℝ} (hc : ContinuousAt h x) :
    Tendsto (fun z : ℂ => (densityCauchyTransform h z).im)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (-Real.pi * h x)) := by
  have hn : ∀ᶠ t in 𝓝 x, |h t| < |h x| + 1 := hc.abs.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hn
  let r := ε/2
  have hr : 0 < r := by dsimp [r]; positivity
  let k : ℝ → ℝ := (Icc (x-r) (x+r)).indicator h
  have hk : Measurable k := hh.indicator measurableSet_Icc
  have hki : Integrable k := hi.indicator measurableSet_Icc
  have hkbound : ∀ t, |k t| ≤ |h x|+1 := by
    intro t
    by_cases ht : t ∈ Icc (x-r) (x+r)
    · dsimp only [k]
      rw [indicator_of_mem ht]
      have hmem : t ∈ ball x ε := by
        rw [mem_ball, Real.dist_eq, abs_lt]
        dsimp [r] at ht
        constructor <;> linarith [ht.1, ht.2]
      exact le_of_lt (hsub hmem)
    · dsimp only [k]
      rw [indicator_of_notMem ht, abs_zero]
      positivity
  have hkc : ContinuousAt k x := by
    apply hc.congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds (by linarith : x-r < x) (by linarith : x < x+r)] with t ht
    exact indicator_of_mem ht h
  have hkx : k x = h x := by
    dsimp only [k]
    exact indicator_of_mem (show x ∈ Icc (x-r) (x+r) from ⟨by linarith, by linarith⟩) h
  have hl := densityCauchy_im_tendsto_upper_bounded hk hki hkbound hkc
  rw [hkx] at hl
  have ho := ((show ContinuousAt (fun z : ℂ => (densityCauchyTransform (outsideDensity h x r) z).im) (x : ℂ) from
    Complex.continuous_im.continuousAt.comp (outsideCauchy_continuousAt hh hi hr)).tendsto).mono_left
      (nhdsWithin_le_nhds (s := {z : ℂ | 0 < z.im}))
  rw [densityCauchyTransform_real] at ho
  have hsum := hl.add ho
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [densityCauchyTransform_split hh hi measurableSet_Icc (ne_of_gt hz), Complex.add_im]
  rfl

theorem densityCauchy_im_tendsto_lower {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {x : ℝ} (hc : ContinuousAt h x) :
    Tendsto (fun z : ℂ => (densityCauchyTransform h z).im)
      (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (Real.pi * h x)) := by
  have ht : Tendsto (starRingEnd ℂ) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (show ContinuousAt (starRingEnd ℂ) (x : ℂ) by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using neg_pos.mpr hz
  have hl := ((densityCauchy_im_tendsto_upper hh hi hc).comp ht).neg
  simpa only [Function.comp_def, densityCauchyTransform_conj, Complex.conj_im, neg_mul, neg_neg] using hl

end AperyMoments
