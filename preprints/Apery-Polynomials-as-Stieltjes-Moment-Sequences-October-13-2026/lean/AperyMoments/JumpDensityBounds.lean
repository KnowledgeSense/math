import AperyMoments.JumpExceptionalSet
import AperyMoments.JumpDensityMeasurable
import AperyMoments.ResolventZeroBound
import AperyMoments.ContinuedDensityBound
import AperyMoments.CorrectionCompactBound

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem reciprocalMomentDensity_zero_bound {α : ℝ} (hα : 0 < α) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x < ε → x ∉ jumpExceptionalSet α →
      reciprocalMomentDensity α x ≤ C / Real.sqrt x := by
  obtain ⟨ε,C,hε,hC,hbound⟩ := momentTransform_zero_bound hα
  refine ⟨ε,C/Real.pi,hε,div_nonneg hC Real.pi_pos.le,?_⟩
  intro x hx hxε he
  let := upperHalfPlane_nhdsWithin_neBot x
  have hl := (momentTransform_im_boundary hα hx he).neg
  simp only [neg_mul, neg_neg] at hl
  have hnx := (complex_norm_tendsto_positive hx).mono_left
    (nhdsWithin_le_nhds (s := {s : ℂ | 0 < s.im}))
  have hr := (tendsto_const_nhds (x := C)).div (Real.continuous_sqrt.continuousAt.tendsto.comp hnx)
    (ne_of_gt (Real.sqrt_pos.mpr hx))
  have hi : Real.pi * reciprocalMomentDensity α x ≤ C / Real.sqrt x :=
    le_of_tendsto_of_tendsto hl hr (by
      filter_upwards [self_mem_nhdsWithin, hnx.eventually (Iio_mem_nhds hxε)] with s hs hsn
      exact (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans (hbound s hs hsn)))
  have hi' := (le_div_iff₀ (Real.sqrt_pos.mpr hx)).mp hi
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hx), le_div_iff₀ Real.pi_pos]
  nlinarith

theorem reciprocalMomentDensity_bounded_away_zero {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc δ 64, x ∉ jumpExceptionalSet α →
      reciprocalMomentDensity α x ≤ C := by
  let b := 2*Real.sqrt α
  let R := 8+α/Real.sqrt δ
  let T := continuedDensityBound b
  let J := correctionCompactBound b R/Real.pi^2
  let C := (2*(T+J))/Real.sqrt δ + T/Real.sqrt δ
  have hb : 0 < b := by dsimp [b]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hT : 0 ≤ T := continuedDensityBound_nonneg hb
  have hJ : 0 ≤ J := div_nonneg (correctionCompactBound_nonneg hb hR) (sq_nonneg _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro x hx he
  have hxp : 0 < x := hδ.trans_le hx.1
  have hxs : Real.sqrt δ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx.1
  have hsp : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hn : x ≠ α := by intro heq; exact he (Or.inl (by simp [heq]))
  have hw := reciprocalRadius_gt hα.le hxp hn
  have hne : reciprocalRadius α x ≠ b+4 := by
    intro heq
    exact he (Or.inr ⟨hxp,heq⟩)
  have ht := continuedDensity_uniform_bound hb hw
  have hh := spectralDensity_le_continued hb.le hw
  have hx8 : Real.sqrt x ≤ 8 := by
    have hs := Real.sq_sqrt hxp.le
    have hp := Real.sqrt_nonneg x
    nlinarith [hx.2]
  have hwr : reciprocalRadius α x - b ≤ R := by
    have hd := div_le_div_of_nonneg_left hα.le hsp hxs
    unfold reciprocalRadius
    dsimp [R]
    linarith
  have hj := continuationCorrection_compact_bound hb hw hne hwr
  rw [reciprocalMomentDensity, ite_eq_left ⟨hxp,hn⟩]
  dsimp only
  by_cases hαx : α < x
  · rw [ite_eq_left hαx]
    have hfirst : spectralDensity b (reciprocalRadius α x)/Real.sqrt x ≤ T/Real.sqrt δ :=
      (div_le_div_of_nonneg_right (hh.trans ht) (Real.sqrt_nonneg x)).trans
        (div_le_div_of_nonneg_left hT hsp hxs)
    have hnon : 0 ≤ 2*(T+J)/Real.sqrt δ := by positivity
    change _ ≤ C
    dsimp [C]
    linarith
  · rw [ite_eq_right hαx]
    have hnum : 2*continuedDensity b (reciprocalRadius α x) - spectralDensity b (reciprocalRadius α x) +
        2*continuationCorrection b (reciprocalRadius α x) ≤ 2*(T+J) := by
      have hn' := spectralDensity_nonneg b (reciprocalRadius α x)
      change continuedDensity b (reciprocalRadius α x) ≤ T at ht
      change continuationCorrection b (reciprocalRadius α x) ≤ J at hj
      linarith
    have hfirst := (div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg x)).trans
      (div_le_div_of_nonneg_left (show 0 ≤ 2*(T+J) by positivity) hsp hxs)
    have hnon : 0 ≤ T/Real.sqrt δ := by positivity
    change _ ≤ C
    dsimp [C]
    linarith

end AperyMoments
