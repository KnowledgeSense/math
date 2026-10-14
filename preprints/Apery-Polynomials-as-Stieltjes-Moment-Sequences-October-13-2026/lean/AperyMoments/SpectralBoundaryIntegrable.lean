import AperyMoments.SpectralHalfLimit

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

def lowerVerticalSequence (a : ℝ) (n : ℕ) : ℂ :=
  (a : ℂ) - Complex.I * ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)

theorem lowerVerticalSequence_re (a : ℝ) (n : ℕ) : (lowerVerticalSequence a n).re = a := by
  simp [lowerVerticalSequence]

theorem lowerVerticalSequence_im (a : ℝ) (n : ℕ) : (lowerVerticalSequence a n).im < 0 := by
  simp only [lowerVerticalSequence, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add, zero_sub]
  exact neg_neg_of_pos (by positivity)

theorem lowerVerticalSequence_tendsto (a : ℝ) :
    Tendsto (lowerVerticalSequence a) atTop (𝓝[{z : ℂ | z.im < 0}] (a : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h := (tendsto_const_nhds (x := (a : ℂ))).sub ((tendsto_const_nhds (x := Complex.I)).mul
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))
    convert h using 1 <;> simp
    funext n
    simp [lowerVerticalSequence]
  · exact Eventually.of_forall (lowerVerticalSequence_im a)

theorem spectralBoundaryHalf_integrable {b a σ : ℝ} (hb2 : b ≤ 2) (hl : -b < a) (hr : a < b)
    (hσ : |σ| = 1) :
    IntervalIntegrable (fun v => arcsineHalfWeight b a v • latticeLowerBoundary (σ * (b - a) * v))
      volume 0 1 := by
  let δ : ℝ := min (b - a) (b + a)
  let R : ℝ := max (b - a) (b + a)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hR4 : R < 4 := max_lt (by linarith) (by linarith)
  have hmeas (n : ℕ) : AEStronglyMeasurable (spectralHalfKernel b (lowerVerticalSequence a n) σ)
      (volume.restrict (Ioo 0 1)) :=
    (spectralHalfKernel_continuousOn (lowerVerticalSequence_im a n)
      (by simpa [lowerVerticalSequence_re] using hl)
      (by simpa [lowerVerticalSequence_re] using hr)).aestronglyMeasurable measurableSet_Ioo
  have hbound (n : ℕ) : ∀ᵐ v : ℝ ∂volume.restrict (Ioo 0 1),
      ‖spectralHalfKernel b (lowerVerticalSequence a n) σ v‖ ≤
        spectralHalfBound δ R * convolutionEndpointWeight v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact spectralHalfKernel_bound hδ hR4 hσ (lowerVerticalSequence_im a n)
      (by simpa only [lowerVerticalSequence_re] using min_le_right (b - a) (b + a))
      (by simpa only [lowerVerticalSequence_re] using min_le_left (b - a) (b + a))
      (by simpa only [lowerVerticalSequence_re] using le_max_left (b - a) (b + a)) hv
  have hlim : ∀ᵐ v : ℝ ∂volume.restrict (Ioo 0 1),
      Tendsto (fun n => spectralHalfKernel b (lowerVerticalSequence a n) σ v) atTop
        (𝓝 (arcsineHalfWeight b a v • latticeLowerBoundary (σ * (b - a) * v))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact (spectralHalfKernel_tendsto hb2 hl hr hσ hv).comp (lowerVerticalSequence_tendsto a)
  have hi : IntegrableOn (fun v => spectralHalfBound δ R * convolutionEndpointWeight v) (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (IntervalIntegrable.const_mul convolutionEndpointWeight_integrable _)
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  exact ⟨aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim,
    hasFiniteIntegral_of_dominated_convergence hi.hasFiniteIntegral hbound hlim⟩

end AperyMoments
