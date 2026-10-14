import AperyMoments.LatticeMoments
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

theorem ellipticK_measurable : Measurable ellipticK := by
  have hm : Measurable (fun p : ℝ × ℝ => (1 - p.1 * Real.sin p.2 ^ 2) ^ (-(1 / 2 : ℝ))) := by fun_prop
  have h := hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 (Real.pi / 2)))
  have he : ellipticK = (fun m : ℝ => ∫ θ in Ioc (0 : ℝ) (Real.pi / 2),
      (1 - m * Real.sin θ ^ 2) ^ (-(1 / 2 : ℝ))) := by
    funext m
    exact intervalIntegral.integral_of_le (by positivity)
  rw [he]
  exact h.measurable

theorem latticeDensity_measurable : Measurable latticeDensity := by
  unfold latticeDensity latticeExpression
  apply Measurable.ite (isOpen_lt continuous_abs continuous_const).measurableSet
  · exact (ellipticK_measurable.comp (by fun_prop)).div_const _
  · exact measurable_const

theorem spectralDensity_measurable (b : ℝ) : Measurable (spectralDensity b) := by
  have hm : Measurable (fun p : ℝ × ℝ => latticeDensity (p.1 - b * Real.cos p.2)) :=
    latticeDensity_measurable.comp (by fun_prop)
  have h := hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 Real.pi))
  have he : spectralDensity b = (fun w : ℝ => Real.pi⁻¹ * ∫ θ in Ioc (0 : ℝ) Real.pi,
      latticeDensity (w - b * Real.cos θ)) := by
    funext w
    unfold spectralDensity
    rw [intervalIntegral.integral_of_le Real.pi_pos.le]
  rw [he]
  exact h.measurable.const_mul _

theorem latticeDensity_eq_zero_of_abs_ge {x : ℝ} (hx : 4 ≤ |x|) : latticeDensity x = 0 := by
  unfold latticeDensity
  exact ite_eq_right (not_lt.mpr hx)

theorem spectralDensity_eq_zero_of_abs_ge {b w : ℝ} (hb : 0 ≤ b) (hw : 4 + b ≤ |w|) :
    spectralDensity b w = 0 := by
  unfold spectralDensity
  have he : (fun θ : ℝ => latticeDensity (w - b * Real.cos θ)) = 0 := by
    funext θ
    apply latticeDensity_eq_zero_of_abs_ge
    have hu : |b * Real.cos θ| ≤ b := by
      rw [abs_mul, abs_of_nonneg hb]
      nlinarith [Real.abs_cos_le_one θ]
    have h := abs_sub_abs_le_abs_sub w (b * Real.cos θ)
    linarith
  rw [he]
  change Real.pi⁻¹ * (∫ _θ in (0 : ℝ)..Real.pi, (0 : ℝ)) = 0
  simp

def spectralTestKernel (b : ℝ) (F : ℝ → ℂ) (θ w : ℝ) : ℂ :=
  F w * (latticeDensity (w - b * Real.cos θ) : ℂ)

theorem spectralTestKernel_measurable (b : ℝ) {F : ℝ → ℂ} (hF : Continuous F) :
    Measurable (fun p : ℝ × ℝ => spectralTestKernel b F p.1 p.2) := by
  unfold spectralTestKernel
  exact (hF.measurable.comp measurable_snd).mul
    (Complex.continuous_ofReal.measurable.comp (latticeDensity_measurable.comp (by fun_prop)))

theorem spectralTestKernel_norm_bound {b M : ℝ} (hb : 0 ≤ b) {F : ℝ → ℂ}
    (hM : ∀ w ∈ Icc (-(4 + b)) (4 + b), ‖F w‖ ≤ M) (θ w : ℝ) :
    ‖spectralTestKernel b F θ w‖ ≤ M * latticeDensity (w - b * Real.cos θ) := by
  unfold spectralTestKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (latticeDensity_nonneg _)]
  by_cases hzero : latticeDensity (w - b * Real.cos θ) = 0
  · simp [hzero]
  · have hx : |w - b * Real.cos θ| < 4 := by
      by_contra h
      exact hzero (latticeDensity_eq_zero_of_abs_ge (le_of_not_gt h))
    have hu : |b * Real.cos θ| ≤ b := by
      rw [abs_mul, abs_of_nonneg hb]
      nlinarith [Real.abs_cos_le_one θ]
    have hw : |w| ≤ 4 + b := by
      have h := abs_add_le (w - b * Real.cos θ) (b * Real.cos θ)
      rw [sub_add_cancel] at h
      linarith
    exact mul_le_mul_of_nonneg_right (hM w (abs_le.mp hw)) (latticeDensity_nonneg _)

theorem latticeDensity_translate_integrable (u : ℝ) : Integrable (fun w => latticeDensity (w - u)) := by
  exact (measurePreserving_sub_right volume u).integrable_comp_of_integrable latticeDensity_integrable

theorem latticeDensity_translate_integral (u : ℝ) : (∫ w : ℝ, latticeDensity (w - u)) = 1 := by
  rw [integral_sub_right_eq_self, latticeDensity_integral]

theorem spectralTestKernel_inner_integrable {b M : ℝ} (hb : 0 ≤ b) {F : ℝ → ℂ}
    (hF : Continuous F) (hM : ∀ w ∈ Icc (-(4 + b)) (4 + b), ‖F w‖ ≤ M) (θ : ℝ) :
    Integrable (spectralTestKernel b F θ) := by
  have hm : Measurable (spectralTestKernel b F θ) :=
    (spectralTestKernel_measurable b hF).comp (measurable_const.prodMk measurable_id)
  exact ((latticeDensity_translate_integrable (b * Real.cos θ)).const_mul M).mono'
    hm.aestronglyMeasurable (Eventually.of_forall (spectralTestKernel_norm_bound hb hM θ))

theorem spectralTestKernel_inner_norm_bound {b M : ℝ} (hb : 0 ≤ b) {F : ℝ → ℂ}
    (hF : Continuous F) (hM : ∀ w ∈ Icc (-(4 + b)) (4 + b), ‖F w‖ ≤ M) (θ : ℝ) :
    (∫ w : ℝ, ‖spectralTestKernel b F θ w‖) ≤ M := by
  calc
    _ ≤ ∫ w : ℝ, M * latticeDensity (w - b * Real.cos θ) := by
      apply integral_mono (spectralTestKernel_inner_integrable hb hF hM θ).norm
        ((latticeDensity_translate_integrable (b * Real.cos θ)).const_mul M)
      exact spectralTestKernel_norm_bound hb hM θ
    _ = _ := by rw [integral_const_mul, latticeDensity_translate_integral, mul_one]

theorem spectralTestKernel_integrable {b M : ℝ} (hb : 0 ≤ b) {F : ℝ → ℂ}
    (hF : Continuous F) (hM : ∀ w ∈ Icc (-(4 + b)) (4 + b), ‖F w‖ ≤ M) :
    Integrable (fun p : ℝ × ℝ => spectralTestKernel b F p.1 p.2)
      ((volume.restrict (Ioc 0 Real.pi)).prod volume) := by
  have hm := (spectralTestKernel_measurable b hF).aestronglyMeasurable
    (μ := (volume.restrict (Ioc 0 Real.pi)).prod volume)
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Eventually.of_forall (spectralTestKernel_inner_integrable hb hF hM)
  · have hi : IntegrableOn (fun _ : ℝ => M) (Ioc 0 Real.pi) := integrableOn_const (hs := measure_Ioc_lt_top.ne)
    apply hi.mono' hm.norm.integral_prod_right'
    exact Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact spectralTestKernel_inner_norm_bound hb hF hM θ

end AperyMoments
