import AperyMoments.ReciprocalCauchyBoundary
import AperyMoments.AuxiliaryOuterBoundary

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

/-- The actual positive jump density; its vanishing beyond an enclosing compact
interval is proved separately, without imposing a sharp endpoint in the definition. -/
def reciprocalMomentDensity (α s : ℝ) : ℝ :=
  if 0 < s ∧ s ≠ α then
    let b := 2 * Real.sqrt α
    let w := reciprocalRadius α s
    if α < s then spectralDensity b w / Real.sqrt s
    else (2 * continuedDensity b w - spectralDensity b w +
      2 * continuationCorrection b w) / Real.sqrt s
  else 0

theorem reciprocalMomentDensity_nonneg {α : ℝ} (hα : 0 ≤ α) (s : ℝ) :
    0 ≤ reciprocalMomentDensity α s := by
  unfold reciprocalMomentDensity
  split_ifs with hs hαs
  · exact div_nonneg (spectralDensity_nonneg _ _) (Real.sqrt_nonneg _)
  · have hw := reciprocalRadius_gt hα hs.1 hs.2
    have hh := spectralDensity_le_continued (show 0 ≤ 2*Real.sqrt α by positivity) hw
    have hT := continuedDensity_nonneg (2*Real.sqrt α) (reciprocalRadius α s)
    have hJ := continuationCorrection_nonneg hw.le
    exact div_nonneg (by linarith) (Real.sqrt_nonneg _)
  · exact le_rfl

theorem reciprocalMomentDensity_support {α s : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : s ∉ Icc 0 64) : reciprocalMomentDensity α s = 0 := by
  by_cases hp : 0 < s
  · have hlarge : 64 < s := by
      by_contra hn
      exact hs ⟨hp.le, le_of_not_gt hn⟩
    have hαs : α < s := by linarith
    have hw := reciprocalRadius_large hα hα1 hlarge
    have hwpos : 0 < reciprocalRadius α s := by have := Real.sqrt_nonneg α; linarith
    rw [reciprocalMomentDensity, ite_eq_left ⟨hp, ne_of_gt hαs⟩]
    dsimp only
    rw [ite_eq_left hαs]
    rw [spectralDensity_eq_zero_of_abs_ge (by positivity)
      (by rw [abs_of_pos hwpos]; exact hw.le), zero_div]
  · simp [reciprocalMomentDensity, hp]

theorem momentTransform_im_boundary_outer {α x : ℝ} (hα : 0 < α) (hx : 0 < x) (hαx : α < x) :
    Tendsto (fun s : ℂ => (momentTransform α s).im)
      (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ)) (𝓝 (-Real.pi * reciprocalMomentDensity α x)) := by
  have hl := outerResolvent_im_tendsto_outer hα hx hαx
  have hn := (complex_norm_tendsto_positive hx).eventually (Ioi_mem_nhds hαx)
  have he : (fun s : ℂ => (outerResolvent α s).im) =ᶠ[𝓝[{s : ℂ | 0 < s.im}] (x : ℂ)]
      (fun s => (momentTransform α s).im) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hn] with s hs hsn
    rw [momentTransform_outer_upper α hs hsn]
  have hv := hl.congr' he
  convert hv using 1
  congr 1
  rw [reciprocalMomentDensity, ite_eq_left ⟨hx, ne_of_gt hαx⟩]
  dsimp only
  rw [ite_eq_left hαx]
  ring

theorem correctionResolvent_im_boundary_inner {α x : ℝ} (hα : 0 < α) (hx : 0 < x)
    (hxα : x < α) (hne : reciprocalRadius α x ≠ 2*Real.sqrt α+4) :
    Tendsto (fun s : ℂ => (2 * Real.pi * Complex.I *
      continuedAuxiliary (2*Real.sqrt α) (reciprocalMap α s) / Complex.sqrt s).im)
      (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ))
      (𝓝 (2*Real.pi*(continuedDensity (2*Real.sqrt α) (reciprocalRadius α x) +
        continuationCorrection (2*Real.sqrt α) (reciprocalRadius α x))/Real.sqrt x)) := by
  have hb : 0 < 2*Real.sqrt α := by positivity
  have hw := reciprocalRadius_gt hα.le hx (ne_of_lt hxα)
  have hH := (continuedAuxiliary_right_boundary hb hw hne).comp (reciprocalMap_tendsto_lower hx hxα)
  have hq : Tendsto Complex.sqrt (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ)) (𝓝 (Real.sqrt x : ℂ)) := by
    simpa only [complexSqrt_ofReal_nonneg hx.le] using
      (Complex.differentiableAt_sqrt (z := (x : ℂ)) (Or.inl hx)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hqn : (Real.sqrt x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hx))
  have hl := Complex.continuous_im.continuousAt.tendsto.comp
    ((hH.const_mul (2*Real.pi*Complex.I)).div hq hqn)
  have hB : ((continuedDensity (2*Real.sqrt α) (reciprocalRadius α x) : ℂ) +
      rightCorrectionComplex (2*Real.sqrt α) (reciprocalRadius α x) / ((Real.pi^2 : ℝ) : ℂ)).re =
      continuedDensity (2*Real.sqrt α) (reciprocalRadius α x) +
        continuationCorrection (2*Real.sqrt α) (reciprocalRadius α x) := by
    rw [Complex.add_re, Complex.ofReal_re, div_eq_mul_inv, ← Complex.ofReal_inv]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [rightCorrectionComplex_re hb hw hne]
    field_simp
  convert hl using 1
  · funext s
    rfl
  · congr 1
    symm
    rw [div_eq_mul_inv, ← Complex.ofReal_inv]
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.im_ofNat, Complex.re_ofNat, zero_mul, mul_zero,
      add_zero, zero_add, sub_zero, mul_one, hB]
    ring

theorem momentTransform_im_boundary_inner {α x : ℝ} (hα : 0 < α) (hx : 0 < x)
    (hxα : x < α) (hne : reciprocalRadius α x ≠ 2*Real.sqrt α+4) :
    Tendsto (fun s : ℂ => (momentTransform α s).im)
      (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ)) (𝓝 (-Real.pi * reciprocalMomentDensity α x)) := by
  have hl := (outerResolvent_im_tendsto_inner hα hx hxα).sub
    (correctionResolvent_im_boundary_inner hα hx hxα hne)
  have hn := (complex_norm_tendsto_positive hx).eventually (Iio_mem_nhds hxα)
  have he : (fun s : ℂ => (outerResolvent α s).im - (2*Real.pi*Complex.I *
      continuedAuxiliary (2*Real.sqrt α) (reciprocalMap α s) / Complex.sqrt s).im) =ᶠ[
      𝓝[{s : ℂ | 0 < s.im}] (x : ℂ)] (fun s => (momentTransform α s).im) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hn] with s hs hsn
    rw [momentTransform_upper α hs, reciprocalResolvent_inner hs hsn, sub_div, Complex.sub_im]
    rfl
  have hv := hl.congr' he
  convert hv using 1
  congr 1
  rw [reciprocalMomentDensity, ite_eq_left ⟨hx, ne_of_lt hxα⟩]
  dsimp only
  rw [ite_eq_right (not_lt.mpr hxα.le)]
  ring

end AperyMoments
