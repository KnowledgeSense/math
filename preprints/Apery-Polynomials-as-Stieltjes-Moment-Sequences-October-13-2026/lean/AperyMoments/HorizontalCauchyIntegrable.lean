import AperyMoments.HorizontalCauchyDecay

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory Asymptotics
open scoped Topology

theorem horizontalKernel_tail_bound (F : ℂ→ℂ) (z : ℂ) (C R c x : ℝ)
    (hC : 0≤C) (hR : 0≤R) (hc : 0<c)
    (hF : ∀w:ℂ,0<w.im→R≤‖w‖→‖F w‖≤C/‖w‖)
    (hx : 2*(|z.re|+R+1)≤|x|) :
    ‖horizontalKernel F z c x‖≤4*C*(1+x^2)⁻¹ := by
  let w := horizontalPoint z c x
  have hwim : 0<w.im := by simpa [w,horizontalPoint] using hc
  have hreal : |x|≤‖w‖+|z.re| := by
    calc |x|=|w.re-z.re| := by simp [w,horizontalPoint]
         _≤|w.re|+|z.re| := abs_sub _ _
         _≤‖w‖+|z.re| := add_le_add (Complex.abs_re_le_norm _) le_rfl
  have hxa : 0 < |x| := by linarith [abs_nonneg z.re]
  have hwhalf : |x|/2≤‖w‖ := by linarith
  have hwR : R≤‖w‖ := by linarith [abs_nonneg z.re]
  have hden : |x|≤‖w-z‖ := by
    have hh := Complex.abs_re_le_norm (w-z)
    simpa [w,horizontalPoint] using hh
  have hnum : ‖F w‖≤C/(|x|/2) :=
    (hF w hwim hwR).trans (div_le_div_of_nonneg_left hC (by positivity) hwhalf)
  have hh := div_le_div₀ (div_nonneg hC (by positivity : 0≤|x|/2)) hnum hxa hden
  change ‖F w/(w-z)‖≤_
  rw [norm_div]
  calc _≤(C/(|x|/2))/|x| := hh
       _=2*C/x^2 := by rw [← sq_abs x]; field
       _≤4*C*(1+x^2)⁻¹ := by
         rw [← div_eq_mul_inv]
         apply (div_le_div_iff₀ (sq_pos_of_ne_zero (abs_pos.mp hxa)) (by positivity)).mpr
         have hx2 : 1≤x^2 := by nlinarith [sq_abs x,abs_nonneg z.re]
         nlinarith [mul_nonneg hC (sub_nonneg.mpr hx2)]

theorem horizontalKernel_integrable (F : ℂ→ℂ) (z : ℂ) (C R c : ℝ)
    (hC : 0≤C) (hR : 0≤R) (hc : 0<c) (hcz : c≠z.im)
    (hhol : ∀v:ℂ,0<v.im→DifferentiableAt ℂ F v)
    (hF : ∀w:ℂ,0<w.im→R≤‖w‖→‖F w‖≤C/‖w‖) :
    Integrable (horizontalKernel F z c) := by
  have hcont := horizontalKernel_continuous F z c hhol hc hcz
  apply hcont.locallyIntegrable.integrable_of_isBigO_cocompact
    (g := fun x:ℝ => (1+x^2)⁻¹) _ (integrable_inv_one_add_sq.integrableAtFilter _)
  apply isBigO_iff.mpr
  refine ⟨4*C,?_⟩
  filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually
    (eventually_ge_atTop (2*(|z.re|+R+1)))] with x hx
  have hb := horizontalKernel_tail_bound F z C R c x hC hR hc hF (by simpa using hx)
  simpa only [Real.norm_eq_abs,abs_of_pos (by positivity : 0<(1+x^2)⁻¹)] using hb

end AperyMoments
