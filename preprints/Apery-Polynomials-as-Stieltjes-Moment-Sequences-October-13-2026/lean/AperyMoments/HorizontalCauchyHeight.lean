import AperyMoments.HorizontalCauchyIntegrable

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology

theorem height_majorant_identity (c x : ℝ) (hc : c≠0) :
    (c^2+x^2)⁻¹=(c^2)⁻¹*(1+(c⁻¹*x)^2)⁻¹ := by
  field_simp

theorem height_majorant_integrable (c : ℝ) (hc : c≠0) :
    Integrable (fun x:ℝ => (c^2+x^2)⁻¹) := by
  have h := (integrable_inv_one_add_mul_sq (inv_ne_zero hc)).const_mul ((c^2)⁻¹)
  simpa only [← height_majorant_identity c _ hc] using h

theorem height_majorant_integral (c : ℝ) (hc : 0<c) :
    (∫ x:ℝ,(c^2+x^2)⁻¹)=Real.pi/c := by
  simp_rw [height_majorant_identity c _ (ne_of_gt hc)]
  rw [integral_const_mul,integral_univ_inv_one_add_mul_sq,abs_of_pos (inv_pos.mpr hc)]
  field_simp

theorem shifted_height_majorant_integrable (a c : ℝ) (hc : c≠0) :
    Integrable (fun x:ℝ => (c^2+(a+x)^2)⁻¹) := by
  exact (height_majorant_integrable c hc).comp_add_left a

theorem shifted_height_majorant_integral (a c : ℝ) (hc : 0<c) :
    (∫ x:ℝ,(c^2+(a+x)^2)⁻¹)=Real.pi/c := by
  exact (integral_add_left_eq_self (fun x:ℝ => (c^2+x^2)⁻¹) a).trans (height_majorant_integral c hc)

theorem horizontal_integral_height_bound (F : ℂ→ℂ) (z : ℂ) (C R c : ℝ)
    (hC : 0≤C) (hR : 0≤R) (hc : 0<c) (hcR : R≤c) (hcz : 2*‖z‖≤c)
    (hhol : ∀v:ℂ,0<v.im→DifferentiableAt ℂ F v)
    (hF : ∀w:ℂ,0<w.im→R≤‖w‖→‖F w‖≤C/‖w‖) :
    ‖∫ x:ℝ,horizontalKernel F z c x‖≤2*C*(Real.pi/c) := by
  have hne : c≠z.im := by have hz := Complex.im_le_norm z; linarith [norm_nonneg z]
  have hI := horizontalKernel_integrable F z C R c hC hR hc hne hhol hF
  have hmaj := (shifted_height_majorant_integrable z.re c (ne_of_gt hc)).const_mul (2*C)
  have hb (x:ℝ) : ‖horizontalKernel F z c x‖≤2*C*(c^2+(z.re+x)^2)⁻¹ := by
    let w := horizontalPoint z c x
    have hw : c≤‖w‖ := by simpa [w,horizontalPoint] using Complex.im_le_norm w
    have hwim : 0<w.im := by simpa [w,horizontalPoint] using hc
    have hn : ‖w‖^2=c^2+(z.re+x)^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      simp [w,horizontalPoint,pow_two]
      ring
    have hb := cauchy_kernel_norm_bound F z w C hC (hc.trans_le hw) (hcz.trans hw)
      (hF w hwim (hcR.trans hw))
    rw [hn,div_eq_mul_inv] at hb
    exact hb
  calc ‖∫ x:ℝ,horizontalKernel F z c x‖≤∫ x:ℝ,‖horizontalKernel F z c x‖ := norm_integral_le_integral_norm _
       _≤∫ x:ℝ,2*C*(c^2+(z.re+x)^2)⁻¹ := integral_mono_ae hI.norm hmaj (Eventually.of_forall hb)
       _=2*C*(Real.pi/c) := by rw [integral_const_mul,shifted_height_majorant_integral z.re c hc]

theorem horizontal_integral_tendsto_height (F : ℂ→ℂ) (z : ℂ) (C R : ℝ)
    (hC : 0≤C) (hR : 0≤R)
    (hhol : ∀v:ℂ,0<v.im→DifferentiableAt ℂ F v)
    (hF : ∀w:ℂ,0<w.im→R≤‖w‖→‖F w‖≤C/‖w‖) :
    Tendsto (fun c:ℝ => ∫ x:ℝ,horizontalKernel F z c x) atTop (𝓝 0) := by
  have ht : Tendsto (fun c:ℝ => 2*C*(Real.pi/c)) atTop (𝓝 0) := by
    have h := tendsto_bdd_div_atTop_nhds_zero (b := Real.pi) (B := Real.pi)
      (Eventually.of_forall (fun _ => le_rfl)) (Eventually.of_forall (fun _ => le_rfl)) tendsto_id
    simpa using h.const_mul (2*C)
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_ge_atTop R,eventually_ge_atTop (2*‖z‖)] with c hc hcR hcz
  exact horizontal_integral_height_bound F z C R c hC hR hc hcR hcz hhol hF

end AperyMoments
