import AperyMoments.AuxiliaryEndpointBound
import AperyMoments.AuxiliaryHolomorphy
import AperyMoments.ContinuedDensityBound

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem spectralDensity_endpoint_bound {b x : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hx : 3*b/4 ≤ x) (hxb : x < b) : spectralDensity b x ≤ auxiliaryEndpointBound b := by
  have ht := (continuedAuxiliary_central_boundary hb hb2 (by linarith) hxb).comp
    (lowerVerticalSequence_tendsto x)
  have hd := ((tendsto_nhds_of_tendsto_nhdsWithin (lowerVerticalSequence_tendsto x)).sub_const
    (b : ℂ)).norm
  have hn : ‖(x : ℂ)-(b : ℂ)‖ < b/2 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hxb)]
    linarith
  have he := hd.eventually (Iio_mem_nhds hn)
  have h := le_of_tendsto ht.norm (show ∀ᶠ n : ℕ in atTop,
      ‖continuedAuxiliary b (lowerVerticalSequence x n)‖ ≤ auxiliaryEndpointBound b from by
    filter_upwards [he] with n hn
    exact continuedAuxiliary_endpoint_bound hb hb2 (lowerVerticalSequence_im x n) hn.le)
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (spectralDensity_nonneg b x)] using h

theorem spectralDensity_bounded {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |spectralDensity b x| ≤ C := by
  have hc : ContinuousOn (fun x : ℝ => reflectedAuxiliary b (x : ℂ)) (Icc 0 (3*b/4)) := by
    apply (reflectedAuxiliary_continuousOn hb hb2).comp (by fun_prop)
    intro x hx
    rw [real_mem_ball_zero_iff, abs_of_nonneg hx.1]
    linarith [hx.2]
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let M := max 0 (max C (max (auxiliaryEndpointBound b)
    (max (continuedDensityBound b) (spectralDensity b b))))
  have hM0 : 0 ≤ M := le_max_left _ _
  have hMC : C ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hMA : auxiliaryEndpointBound b ≤ M := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hMT : continuedDensityBound b ≤ M := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hMb : spectralDensity b b ≤ M := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hp : ∀ x : ℝ, 0 ≤ x → spectralDensity b x ≤ M := by
    intro x hx
    by_cases hxc : x ≤ 3*b/4
    · have hh := hC x ⟨hx,hxc⟩
      rw [reflectedAuxiliary_ofReal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (spectralDensity_nonneg b x)] at hh
      exact hh.trans hMC
    · rcases lt_trichotomy x b with hxb | hxb | hxb
      · exact (spectralDensity_endpoint_bound hb hb2 (by linarith) hxb).trans hMA
      · simpa only [hxb] using hMb
      · exact ((spectralDensity_le_continued hb.le hxb).trans
          (continuedDensity_uniform_bound hb hxb)).trans hMT
  refine ⟨M,hM0,fun x => ?_⟩
  rw [abs_of_nonneg (spectralDensity_nonneg b x)]
  by_cases hx : 0 ≤ x
  · exact hp x hx
  · have hh := hp (-x) (by linarith)
    rwa [spectralDensity_neg] at hh

end AperyMoments
