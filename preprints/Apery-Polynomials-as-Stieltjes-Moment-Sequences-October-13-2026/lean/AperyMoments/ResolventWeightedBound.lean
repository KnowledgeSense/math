import AperyMoments.WeightedQuotientBound
import AperyMoments.ReciprocalHorizontalGeometry
import AperyMoments.AuxiliaryCompactBound
import AperyMoments.CauchyImaginaryBound
import AperyMoments.CauchyWeakBound
import AperyMoments.MomentTransform

noncomputable section
namespace AperyMoments

theorem momentTransform_weighted_quotient_bound {α δ N K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hδ : 0 < δ) (hK : 0 ≤ K)
    (hKi : ∀ z : ℂ, |(spectralCauchyTransform (2*Real.sqrt α) z).im| ≤ K)
    {s : ℂ} (hs : 0 < s.im) (hs1 : s.im ≤ 1) (hre : 0 ≤ s.re)
    (hl : δ ≤ ‖s‖) (hu : ‖s‖ ≤ N) (hne : ‖s‖ ≠ α) :
    |(momentTransform α s).im|+s.im*‖momentTransform α s‖ ≤
      (K+2*(2*Real.pi*auxiliaryRightBound (2*Real.sqrt α) (Real.sqrt N+α/Real.sqrt δ)))/Real.sqrt δ +
        s.im*‖spectralCauchyTransform (2*Real.sqrt α) (reciprocalMap α s)‖*
          (1/Real.sqrt δ+1/(Real.sqrt δ)^3) := by
  let b := 2*Real.sqrt α
  let R := Real.sqrt N+α/Real.sqrt δ
  let H := 2*Real.pi*auxiliaryRightBound b R
  have hb : 0 < b := by dsimp [b]; positivity
  have hb2 : b ≤ 2 := by
    dsimp only [b]
    have hh : Real.sqrt α ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hα1
    linarith
  have hH : 0 ≤ H := mul_nonneg (by positivity) (auxiliaryRightBound_nonneg hb)
  have hr : b/2 ≤ (reciprocalMap α s).re := by
    simpa only [b, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      reciprocalMap_re_lower_positive hα.le hs hre
  have hR : ‖reciprocalMap α s‖ ≤ R := reciprocalMap_norm_bound hα.le hδ hs hl hu
  have hd := Real.sqrt_pos.mpr hδ
  have hq := sqrt_upper_norm_lower hδ hs hl
  have hqi := sqrt_upper_im_bound hδ hs hre hl
  rw [momentTransform_upper α hs]
  rcases lt_or_gt_of_ne hne with hinner | houter
  · rw [reciprocalResolvent_inner hs hinner]
    have haux := continuedAuxiliary_right_bound hb hb2 ((reciprocalMap_im_sign hs α).1.mpr hinner) hr hR
    have hE : ‖(2*Real.pi*Complex.I)*continuedAuxiliary b (reciprocalMap α s)‖ ≤ H := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      exact mul_le_mul_of_nonneg_left haux (by positivity)
    exact weighted_quotient_bound hd hq hs.le hs1 hK (hKi _) hH hE hqi
  · rw [reciprocalResolvent_outer hs houter]
    have he := weighted_quotient_bound (A := spectralCauchyTransform b (reciprocalMap α s))
      (E := 0) hd hq hs.le hs1 hK (hKi _) hH (by simpa using hH) hqi
    simpa only [sub_zero] using he

theorem momentTransform_weighted_bound {α δ N : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 < s.im → s.im ≤ 1 → 0 ≤ s.re →
      δ ≤ ‖s‖ → ‖s‖ ≤ N → ‖s‖ ≠ α →
      |(momentTransform α s).im|+s.im*‖momentTransform α s‖ ≤
        C*(1+s.im*|(reciprocalMap α s).im|^(-(1/3 : ℝ))) := by
  let b := 2*Real.sqrt α
  have hb : 0 < b := by dsimp [b]; positivity
  have hb2 : b ≤ 2 := by
    dsimp only [b]
    have hh : Real.sqrt α ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hα1
    linarith
  obtain ⟨K,hK,hKi⟩ := spectralCauchy_im_bounded hb hb2
  let H := 2*Real.pi*auxiliaryRightBound b (Real.sqrt N+α/Real.sqrt δ)
  let D := (K+2*H)/Real.sqrt δ
  let L := 1/Real.sqrt δ+1/(Real.sqrt δ)^3
  let G₀ := spectralFourthIntegral b/4
  let G₁ := cauchyStudentIntegral/(4/3)
  have hH : 0 ≤ H := mul_nonneg (by positivity) (auxiliaryRightBound_nonneg hb)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hG₀ : 0 ≤ G₀ := div_nonneg (spectralFourthIntegral_nonneg b) (by norm_num)
  have hG₁ : 0 ≤ G₁ := div_nonneg cauchyStudentIntegral_nonneg (by norm_num)
  refine ⟨D+L*(G₀+G₁),add_nonneg hD (mul_nonneg hL (add_nonneg hG₀ hG₁)),?_⟩
  intro s hs hs1 hre hl hu hne
  let p := |(reciprocalMap α s).im|^(-(1/3 : ℝ))
  have hp : 0 ≤ p := Real.rpow_nonneg (abs_nonneg _) _
  have hi : (reciprocalMap α s).im ≠ 0 := by
    intro he
    exact hne ((reciprocalMap_im_sign hs α).2.1.mp he)
  have hg := spectralCauchyTransform_weak_bound hb.le hi
  have hg' : ‖spectralCauchyTransform b (reciprocalMap α s)‖ ≤ G₀+G₁*p := by
    convert hg using 1; dsimp [G₀,G₁,p]; ring
  have hw := momentTransform_weighted_quotient_bound hα hα1 hδ hK hKi hs hs1 hre hl hu hne
  change |(momentTransform α s).im|+s.im*‖momentTransform α s‖ ≤
    D+s.im*‖spectralCauchyTransform b (reciprocalMap α s)‖*L at hw
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg' hs.le) hL
  have hsmall := mul_le_mul_of_nonneg_right hs1 (mul_nonneg hL hG₀)
  have hrest : 0 ≤ (D+L*G₀)*s.im*p := by positivity
  have hremain : 0 ≤ L*G₁ := mul_nonneg hL hG₁
  change _ ≤ (D+L*(G₀+G₁))*(1+s.im*p)
  nlinarith

end AperyMoments
