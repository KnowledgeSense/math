import AperyMoments.SpectralCentralBoundary
import AperyMoments.SpectralSymmetry
import Mathlib.Analysis.Calculus.Deriv.Star

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

/-- Schwarz reflection with the actual central density as the real-axis value. -/
def reflectedAuxiliary (b : ℝ) (z : ℂ) : ℂ :=
  if z.im < 0 then continuedAuxiliary b z
  else if 0 < z.im then starRingEnd ℂ (continuedAuxiliary b (starRingEnd ℂ z))
  else (spectralDensity b z.re : ℂ)

theorem reflectedAuxiliary_ofReal (b x : ℝ) :
    reflectedAuxiliary b (x : ℂ) = (spectralDensity b x : ℂ) := by
  simp [reflectedAuxiliary]

theorem reflectedAuxiliary_lower {b : ℝ} {z : ℂ} (hz : z.im < 0) :
    reflectedAuxiliary b z = continuedAuxiliary b z := by
  simp [reflectedAuxiliary, hz]

theorem reflectedAuxiliary_upper {b : ℝ} {z : ℂ} (hz : 0 < z.im) :
    reflectedAuxiliary b z = starRingEnd ℂ (continuedAuxiliary b (starRingEnd ℂ z)) := by
  simp [reflectedAuxiliary, hz, not_lt.mpr hz.le]

theorem reflectedAuxiliary_lower_differentiableAt {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : z.im < 0) :
    DifferentiableAt ℂ (reflectedAuxiliary b) z := by
  apply (continuedAuxiliary_analyticOnNhd hb z hz).differentiableAt.congr_of_eventuallyEq
  filter_upwards [Complex.continuous_im.continuousAt.eventually (Iio_mem_nhds hz)] with w hw
  exact reflectedAuxiliary_lower hw

theorem reflectedAuxiliary_upper_differentiableAt {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (reflectedAuxiliary b) z := by
  have hc : (starRingEnd ℂ z).im < 0 := by simpa using neg_neg_of_pos hz
  have hd := (continuedAuxiliary_analyticOnNhd hb (starRingEnd ℂ z) hc).differentiableAt.conj_conj
  simp only [starRingEnd_apply, star_star] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Complex.continuous_im.continuousAt.eventually (Ioi_mem_nhds hz)] with w hw
  exact reflectedAuxiliary_upper hw

theorem reflectedAuxiliary_lower_boundary {b a : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hl : -b < a) (hr : a < b) :
    Tendsto (reflectedAuxiliary b) (𝓝[{z : ℂ | z.im < 0}] (a : ℂ))
      (𝓝 (reflectedAuxiliary b (a : ℂ))) := by
  rw [reflectedAuxiliary_ofReal]
  apply (continuedAuxiliary_central_boundary hb hb2 hl hr).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (reflectedAuxiliary_lower hz).symm

theorem conjugate_upper_tendsto (a : ℝ) :
    Tendsto (starRingEnd ℂ) (𝓝[{z : ℂ | 0 < z.im}] (a : ℂ))
      (𝓝[{z : ℂ | z.im < 0}] (a : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using (show ContinuousAt (starRingEnd ℂ) (a : ℂ) by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using neg_neg_of_pos hz

theorem reflectedAuxiliary_upper_boundary {b a : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hl : -b < a) (hr : a < b) :
    Tendsto (reflectedAuxiliary b) (𝓝[{z : ℂ | 0 < z.im}] (a : ℂ))
      (𝓝 (reflectedAuxiliary b (a : ℂ))) := by
  rw [reflectedAuxiliary_ofReal]
  have h := ((show Continuous (starRingEnd ℂ) by fun_prop).continuousAt.tendsto.comp
    ((continuedAuxiliary_central_boundary hb hb2 hl hr).comp (conjugate_upper_tendsto a)))
  simp only [Complex.conj_ofReal] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (reflectedAuxiliary_upper hz).symm

theorem reflectedAuxiliary_conj (b : ℝ) (z : ℂ) :
    reflectedAuxiliary b (starRingEnd ℂ z) = starRingEnd ℂ (reflectedAuxiliary b z) := by
  by_cases hl : z.im < 0
  · rw [reflectedAuxiliary_upper (by simpa using neg_pos.mpr hl), reflectedAuxiliary_lower hl]
    simp
  · by_cases hu : 0 < z.im
    · rw [reflectedAuxiliary_lower (by simpa using neg_neg_of_pos hu), reflectedAuxiliary_upper hu]
      simp
    · have hz : z.im = 0 := le_antisymm (le_of_not_gt hu) (le_of_not_gt hl)
      simp [reflectedAuxiliary, hz]

end AperyMoments
