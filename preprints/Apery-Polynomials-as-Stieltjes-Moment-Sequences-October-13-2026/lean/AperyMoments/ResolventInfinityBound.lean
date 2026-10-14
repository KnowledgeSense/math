import AperyMoments.ResolventZeroBound

noncomputable section
open Set MeasureTheory
namespace AperyMoments

/-- The actual transform has the inverse-linear decay required by the horizontal
Cauchy formula, uniformly throughout the upper half-plane. -/
theorem momentTransform_infinity_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {s : ℂ} (hs : 0 < s.im) (hn : 256 ≤ ‖s‖) :
    ‖momentTransform α s‖ ≤ 2 / ‖s‖ := by
  let q := ‖Complex.sqrt s‖
  let b := 2*Real.sqrt α
  have hq0 : 0 ≤ q := norm_nonneg _
  have hqs : q^2 = ‖s‖ := sqrt_upper_norm hs
  have hq : 16 ≤ q := by nlinarith
  have hqp : 0 < q := by linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb2 : b ≤ 2 := by
    have he : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
    dsimp [b]
    linarith
  have hr := norm_sub_le (reciprocalMap α s) ((α : ℂ)/Complex.sqrt s)
  rw [show reciprocalMap α s - (α : ℂ)/Complex.sqrt s = Complex.sqrt s by unfold reciprocalMap; ring,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα] at hr
  change q ≤ ‖reciprocalMap α s‖ + α/q at hr
  have hd : α/q ≤ 1 := (div_le_iff₀ hqp).mpr (by linarith)
  have hhalf : q/2 ≤ ‖reciprocalMap α s‖-(4+b) := by linarith
  have hrp : 4+b < ‖reciprocalMap α s‖ := by linarith
  have hg := spectralCauchyTransform_norm_bound hb hrp
  have hg' : ‖spectralCauchyTransform b (reciprocalMap α s)‖ ≤ 2/q := by
    apply hg.trans
    calc
      1/(‖reciprocalMap α s‖-(4+b)) ≤ 1/(q/2) :=
        div_le_div_of_nonneg_left zero_le_one (by linarith) hhalf
      _ = 2/q := by field_simp
  rw [momentTransform_upper α hs, reciprocalResolvent_outer hs (by linarith), norm_div]
  change ‖spectralCauchyTransform b (reciprocalMap α s)‖ / q ≤ 2/‖s‖
  apply (div_le_div_of_nonneg_right hg' hq0).trans_eq
  rw [← hqs]
  field_simp

end AperyMoments
