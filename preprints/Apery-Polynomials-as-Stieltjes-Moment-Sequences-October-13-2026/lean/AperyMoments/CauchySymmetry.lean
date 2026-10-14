import AperyMoments.ContinuedCauchy
import AperyMoments.AuxiliarySymmetry

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

theorem densityCauchyTransform_conj (h : ℝ → ℝ) (z : ℂ) :
    densityCauchyTransform h (starRingEnd ℂ z) = starRingEnd ℂ (densityCauchyTransform h z) := by
  unfold densityCauchyTransform densityCauchyKernel
  rw [← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by simp)

theorem densityCauchyTransform_neg {h : ℝ → ℝ} (he : ∀ t, h (-t) = h t) (z : ℂ) :
    densityCauchyTransform h (-z) = -densityCauchyTransform h z := by
  unfold densityCauchyTransform
  rw [← integral_neg_eq_self (μ := volume) (densityCauchyKernel h (-z)), ← integral_neg]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  simp only [densityCauchyKernel, he, Complex.ofReal_neg]
  rw [show -z - -(t : ℂ) = -(z - t) by ring, div_neg]

theorem spectralCauchyTransform_imaginary (b y : ℝ) :
    (spectralCauchyTransform b (Complex.I * (y : ℂ))).re = 0 := by
  have hc := densityCauchyTransform_conj (spectralDensity b) (Complex.I * (y : ℂ))
  have hn := densityCauchyTransform_neg (spectralDensity_neg b) (Complex.I * (y : ℂ))
  have he : starRingEnd ℂ (Complex.I * (y : ℂ)) = -(Complex.I * (y : ℂ)) := by simp
  rw [he, hn] at hc
  have hr := congrArg Complex.re hc
  change -(spectralCauchyTransform b (Complex.I * (y : ℂ))).re =
    (spectralCauchyTransform b (Complex.I * (y : ℂ))).re at hr
  linarith

theorem continuedCauchy_imaginary_nonzero {b y : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hy : y ≠ 0) : (continuedCauchy b (Complex.I * (y : ℂ))).re = 0 := by
  rcases lt_or_gt_of_ne hy with hy | hy
  · rw [continuedCauchy_lower b (by simpa using hy)]
    have hH := continuedAuxiliary_negative_imaginary_real hb hb2 (neg_pos.mpr hy)
    have he : -Complex.I * ((-y : ℝ) : ℂ) = Complex.I * (y : ℂ) := by simp
    rw [he] at hH
    simp [Complex.mul_re, Complex.mul_im, hH, spectralCauchyTransform_imaginary]
  · rw [continuedCauchy_upper b (by simpa using hy)]
    exact spectralCauchyTransform_imaginary b y

theorem continuedCauchy_imaginary {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 2) (y : ℝ) :
    (continuedCauchy b (Complex.I * (y : ℂ))).re = 0 := by
  by_cases hy : y = 0
  · subst y
    simp only [Complex.ofReal_zero, mul_zero]
    have hc := (continuedCauchy_analyticAt_real hb hb2 (by simpa using hb : |(0 : ℝ)| < b)).continuousAt
    have hc' : ContinuousAt (continuedCauchy b) (Complex.I * ((0 : ℝ) : ℂ)) := by simpa using hc
    have ht : Tendsto (fun t : ℝ => (continuedCauchy b (Complex.I * (t : ℂ))).re)
        (𝓝[>] (0 : ℝ)) (𝓝 ((continuedCauchy b 0).re)) := by
      have hcomp := Complex.continuous_re.continuousAt.comp
        (hc'.comp (f := fun t : ℝ => Complex.I * (t : ℂ)) (show ContinuousAt (fun t : ℝ => Complex.I * (t : ℂ)) 0 by fun_prop))
      simpa only [Function.comp_def, Complex.ofReal_zero, mul_zero] using hcomp.tendsto.mono_left nhdsWithin_le_nhds
    have hz : Tendsto (fun t : ℝ => (continuedCauchy b (Complex.I * (t : ℂ))).re)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (continuedCauchy_imaginary_nonzero hb hb2 (ne_of_gt ht)).symm
    exact tendsto_nhds_unique ht hz
  · exact continuedCauchy_imaginary_nonzero hb hb2 hy

end AperyMoments
