import AperyMoments.SpectralBoundaryValue

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem negative_conjugate_lower_tendsto (a : ℝ) :
    Tendsto (fun w : ℂ => -starRingEnd ℂ w)
      (𝓝[{z : ℂ | z.im < 0}] (a : ℂ)) (𝓝[{z : ℂ | z.im < 0}] (-(a : ℂ))) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using (show ContinuousAt (fun w : ℂ => -starRingEnd ℂ w) (a : ℂ) by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    simpa using hw

/-- The full central boundary value of the genuine lower arcsine convolution. -/
theorem continuedSpectral_central_boundary {b a : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hl : -b < a) (hr : a < b) :
    Tendsto (continuedSpectral b) (𝓝[{z : ℂ | z.im < 0}] (a : ℂ))
      (𝓝 ((spectralDensity b a : ℂ) + Complex.I * (centralCorrection b a : ℂ) / (Real.pi ^ 2 : ℝ))) := by
  have hright := spectralHalfIntegral_boundary hb2 hl hr (by norm_num : |(-1 : ℝ)| = 1)
  have hleft := (spectralHalfIntegral_boundary hb2 (by linarith : -b < -a) (by linarith : -a < b)
    (by norm_num : |(1 : ℝ)| = 1)).comp (by simpa only [Complex.ofReal_neg] using negative_conjugate_lower_tendsto a)
  have ht := (hleft.add hright).const_mul (Real.pi : ℂ)⁻¹
  have he : (Real.pi : ℂ)⁻¹ *
      ((∫ v in (0 : ℝ)..1, arcsineHalfWeight b (-a) v • latticeLowerBoundary (1 * (b - -a) * v)) +
      (∫ v in (0 : ℝ)..1, arcsineHalfWeight b a v • latticeLowerBoundary (-1 * (b - a) * v))) =
      (spectralDensity b a : ℂ) + Complex.I * (centralCorrection b a : ℂ) / (Real.pi ^ 2 : ℝ) := by
    rw [← spectralBoundary_value hb hb2 hl hr]
    congr 1
    rw [arcsine_split hb hl hr (fun u => latticeLowerBoundary (a - u))
      (spectralBoundary_angular_integrable hb hb2 hl hr)]
    congr 1
    · apply intervalIntegral.integral_congr
      intro v _
      dsimp only
      rw [show a - (a - (b + a) * v) = 1 * (b - -a) * v by ring]
    · apply intervalIntegral.integral_congr
      intro v _
      dsimp only
      rw [show a - (a + (b - a) * v) = -1 * (b - a) * v by ring]
  rw [he] at ht
  apply ht.congr'
  have hreal : Tendsto (fun w : ℂ => w.re) (𝓝[{z : ℂ | z.im < 0}] (a : ℂ)) (𝓝 a) :=
    Complex.continuous_re.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [hreal.eventually (Ioo_mem_nhds hl hr), self_mem_nhdsWithin] with w hw hwim
  exact (continuedSpectral_split hb hwim hw.1 hw.2).symm

/-- The analytic correction subtracts precisely the unwanted imaginary central boundary. -/
def continuedAuxiliary (b : ℝ) (w : ℂ) : ℂ :=
  continuedSpectral b w - Complex.I * continuedCorrection b w / ((Real.pi ^ 2 : ℝ) : ℂ)

theorem continuedAuxiliary_central_boundary {b a : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hl : -b < a) (hr : a < b) :
    Tendsto (continuedAuxiliary b) (𝓝[{z : ℂ | z.im < 0}] (a : ℂ))
      (𝓝 (spectralDensity b a : ℂ)) := by
  have h := (continuedSpectral_central_boundary hb hb2 hl hr).sub
    (((continuedCorrection_central_boundary hb hb2 hl hr).const_mul Complex.I).div_const
      ((Real.pi ^ 2 : ℝ) : ℂ))
  unfold continuedAuxiliary
  simpa only [add_sub_cancel_right] using h

theorem continuedAuxiliary_analyticOnNhd {b : ℝ} (hb : 0 < b) :
    AnalyticOnNhd ℂ (continuedAuxiliary b) {z : ℂ | z.im < 0} := by
  intro z hz
  exact (continuedSpectral_analyticOnNhd hb.le z (Or.inl hz)).sub
    (((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => Complex.I) z).mul
      (continuedCorrection_analyticOnNhd hb z hz)).div_const)

end AperyMoments
