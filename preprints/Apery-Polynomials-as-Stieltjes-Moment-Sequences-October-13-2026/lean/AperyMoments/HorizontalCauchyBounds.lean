import AperyMoments.HorizontalCauchyStrip

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology Interval

theorem dslope_norm_le (F : ℂ→ℂ) (z w : ℂ) (r M : ℝ)
    (hr : 0<r) (hd : r≤‖w-z‖) (hF : ‖F w‖≤M) :
    ‖dslope F z w‖≤(M+‖F z‖)/r := by
  have hw : w≠z := sub_ne_zero.mp (norm_pos_iff.mp (hr.trans_le hd))
  rw [dslope_of_ne F hw,slope_def_field,norm_div]
  exact div_le_div₀ (add_nonneg ((norm_nonneg _).trans hF) (norm_nonneg _))
    ((norm_sub_le (F w) (F z)).trans (add_le_add hF le_rfl)) hr hd

theorem vertical_distance_right (z : ℂ) (r y : ℝ) :
    |r|≤‖((z.re+r:ℝ)+y*I:ℂ)-z‖ := by
  have h := Complex.abs_re_le_norm (((z.re+r:ℝ)+y*I:ℂ)-z)
  simpa using h

theorem vertical_distance_left (z : ℂ) (r y : ℝ) :
    |r|≤‖((z.re-r:ℝ)+y*I:ℂ)-z‖ := by
  have h := Complex.abs_re_le_norm (((z.re-r:ℝ)+y*I:ℂ)-z)
  simpa using h

theorem norm_vertical_dslope_integral_right (F : ℂ→ℂ) (z : ℂ) (r M c d : ℝ)
    (hr : 0<r) (hF : ∀y∈Ι c d,‖F ((z.re+r:ℝ)+y*I)‖≤M) :
    ‖∫ y:ℝ in c..d,dslope F z ((z.re+r:ℝ)+y*I)‖≤(M+‖F z‖)/r*|d-c| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro y hy
  apply dslope_norm_le F z _ r M hr _ (hF y hy)
  simpa only [abs_of_pos hr] using vertical_distance_right z r y

theorem norm_vertical_dslope_integral_left (F : ℂ→ℂ) (z : ℂ) (r M c d : ℝ)
    (hr : 0<r) (hF : ∀y∈Ι c d,‖F ((z.re-r:ℝ)+y*I)‖≤M) :
    ‖∫ y:ℝ in c..d,dslope F z ((z.re-r:ℝ)+y*I)‖≤(M+‖F z‖)/r*|d-c| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro y hy
  apply dslope_norm_le F z _ r M hr _ (hF y hy)
  simpa only [abs_of_pos hr] using vertical_distance_left z r y

theorem vertical_dslope_limit_right_of_bounded (F : ℂ→ℂ) (z : ℂ) (M c d : ℝ)
    (hF : ∀ᶠr:ℝ in atTop,∀y∈Ι c d,‖F ((z.re+r:ℝ)+y*I)‖≤M) :
    Tendsto (fun r:ℝ => ∫ y:ℝ in c..d,dslope F z ((z.re+r:ℝ)+y*I)) atTop (𝓝 0) := by
  have ht : Tendsto (fun r:ℝ => (M+‖F z‖)/r*|d-c|) atTop (𝓝 0) := by
    have h := tendsto_bdd_div_atTop_nhds_zero
      (b := M+‖F z‖) (B := M+‖F z‖)
      (Eventually.of_forall (fun _ => le_rfl)) (Eventually.of_forall (fun _ => le_rfl)) tendsto_id
    simpa using h.mul_const |d-c|
  apply squeeze_zero_norm' _ ht
  filter_upwards [hF,eventually_gt_atTop (0:ℝ)] with r hfr hr
  exact norm_vertical_dslope_integral_right F z r M c d hr hfr

theorem vertical_dslope_limit_left_of_bounded (F : ℂ→ℂ) (z : ℂ) (M c d : ℝ)
    (hF : ∀ᶠr:ℝ in atTop,∀y∈Ι c d,‖F ((z.re-r:ℝ)+y*I)‖≤M) :
    Tendsto (fun r:ℝ => ∫ y:ℝ in c..d,dslope F z ((z.re-r:ℝ)+y*I)) atTop (𝓝 0) := by
  have ht : Tendsto (fun r:ℝ => (M+‖F z‖)/r*|d-c|) atTop (𝓝 0) := by
    have h := tendsto_bdd_div_atTop_nhds_zero
      (b := M+‖F z‖) (B := M+‖F z‖)
      (Eventually.of_forall (fun _ => le_rfl)) (Eventually.of_forall (fun _ => le_rfl)) tendsto_id
    simpa using h.mul_const |d-c|
  apply squeeze_zero_norm' _ ht
  filter_upwards [hF,eventually_gt_atTop (0:ℝ)] with r hfr hr
  exact norm_vertical_dslope_integral_left F z r M c d hr hfr

end AperyMoments
