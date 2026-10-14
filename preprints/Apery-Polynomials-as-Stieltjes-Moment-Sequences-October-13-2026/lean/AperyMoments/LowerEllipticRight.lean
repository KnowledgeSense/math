import AperyMoments.LowerEllipticInversion
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def halfEllipticIntegral (z : ℂ) : ℂ := 2 * ∫ t in (0 : ℝ)..1, lowerEllipticKernel z t

theorem rightEllipticKernel_bases_mem_slitPlane {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    (t : ℂ) ^ 2 + z ∈ Complex.slitPlane ∧ 1 + z * (t : ℂ) ^ 2 ∈ Complex.slitPlane := by
  constructor <;> apply Complex.mem_slitPlane_iff.mpr <;> left
  · rw [← Complex.ofReal_pow]
    simp only [Complex.add_re, Complex.ofReal_re]
    positivity
  · rw [← Complex.ofReal_pow]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    positivity

theorem rightEllipticKernel_continuous {z : ℂ} (hz : 0 < z.re) :
    Continuous (lowerEllipticKernel z) := by
  unfold lowerEllipticKernel
  exact (Continuous.cpow (by fun_prop) continuous_const
    (fun t => (rightEllipticKernel_bases_mem_slitPlane hz t).1)).mul
    (Continuous.cpow (by fun_prop) continuous_const
      (fun t => (rightEllipticKernel_bases_mem_slitPlane hz t).2))

theorem lowerEllipticIntegral_eq_half_right {z : ℂ} (hz : 0 < z.re) :
    lowerEllipticIntegral z = halfEllipticIntegral z :=
  lowerEllipticIntegral_half_of_integrable (lowerEllipticKernel_integrableOn_of_first z
    ((rightEllipticKernel_continuous hz).intervalIntegrable _ _))

theorem rightEllipticKernel_hasDerivAt {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    HasDerivAt (fun z => lowerEllipticKernel z t) (lowerEllipticKernelDerivative z t) z := by
  obtain ⟨hA, hB⟩ := rightEllipticKernel_bases_mem_slitPlane hz t
  have ha := ((hasDerivAt_const z ((t : ℂ)^2)).add (hasDerivAt_id z)).cpow_const
    (c := -(1/2:ℂ)) hA
  have hb := (((hasDerivAt_id z).mul_const ((t : ℂ)^2)).const_add 1).cpow_const
    (c := -(1/2:ℂ)) hB
  convert ha.mul hb using 1
  · rfl
  · simp only [lowerEllipticKernelDerivative, lowerEllipticKernel, Pi.add_apply, id_eq, zero_add, one_mul, mul_one]
    rw [Complex.cpow_sub _ _ (Complex.slitPlane_ne_zero hA),
      Complex.cpow_sub _ _ (Complex.slitPlane_ne_zero hB)]
    simp only [Complex.cpow_one, div_eq_mul_inv]
    ring

theorem rightEllipticKernelDerivative_continuousOn :
    ContinuousOn (fun p : ℂ × ℝ => lowerEllipticKernelDerivative p.1 p.2)
      ({z : ℂ | 0 < z.re} ×ˢ univ) := by
  unfold lowerEllipticKernelDerivative lowerEllipticKernel
  apply ContinuousOn.mul
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.mul
    · exact ContinuousOn.cpow_const (by fun_prop)
        (fun p hp => (rightEllipticKernel_bases_mem_slitPlane hp.1 p.2).1)
    · exact ContinuousOn.cpow_const (by fun_prop)
        (fun p hp => (rightEllipticKernel_bases_mem_slitPlane hp.1 p.2).2)
  · apply ContinuousOn.add
    · exact ContinuousOn.inv₀ (by fun_prop)
        (fun p hp => Complex.slitPlane_ne_zero (rightEllipticKernel_bases_mem_slitPlane hp.1 p.2).1)
    · exact ContinuousOn.mul (by fun_prop) (ContinuousOn.inv₀ (by fun_prop)
        (fun p hp => Complex.slitPlane_ne_zero (rightEllipticKernel_bases_mem_slitPlane hp.1 p.2).2))

theorem rightEllipticKernelDerivative_continuous {z : ℂ} (hz : 0 < z.re) :
    Continuous (lowerEllipticKernelDerivative z) := by
  have h := rightEllipticKernelDerivative_continuousOn.comp
    (show ContinuousOn (fun t : ℝ => (z, t)) univ by fun_prop)
    (fun _ _ => ⟨hz, mem_univ _⟩)
  exact continuousOn_univ.mp h

theorem halfEllipticIntegral_differentiableAt {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ halfEllipticIntegral z := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  obtain ⟨ε, hε, he⟩ := Metric.isOpen_iff.mp hopen z hz
  have hc : Metric.closedBall z (ε / 2) ⊆ {z : ℂ | 0 < z.re} :=
    (Metric.closedBall_subset_ball (by linarith)).trans he
  have hcompact := (isCompact_closedBall z (ε / 2)).prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    (rightEllipticKernelDerivative_continuousOn.mono (fun p hp => ⟨hc hp.1, mem_univ _⟩))
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := lowerEllipticKernel) (F' := lowerEllipticKernelDerivative) (μ := volume)
    (bound := fun _ => C) (a := 0) (b := 1)
    (s := Metric.ball z (ε / 2)) (Metric.ball_mem_nhds z (by linarith))
    (by
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact (rightEllipticKernel_continuous hw).aestronglyMeasurable)
    ((rightEllipticKernel_continuous hz).intervalIntegrable _ _)
    (rightEllipticKernelDerivative_continuous hz).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ht w hw => hC (w, t)
      ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hw).le, by
        rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        exact ⟨ht.1.le, ht.2⟩⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ w hw => rightEllipticKernel_hasDerivAt
      (hc (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hw).le)) t)
  exact hd.2.differentiableAt.const_mul 2

theorem halfEllipticIntegral_analyticOnNhd :
    AnalyticOnNhd ℂ halfEllipticIntegral {z : ℂ | 0 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  exact (halfEllipticIntegral_differentiableAt hz).differentiableWithinAt

theorem rightElliptic_parameter_mem_domain {z : ℂ} (hz : 0 < z.re) :
    1 - z ^ 2 ∈ ellipticDomain := by
  by_cases him : z.im = 0
  · right
    simp only [Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re, him, mul_zero, sub_zero]
    nlinarith
  · left
    simp only [Complex.sub_im, Complex.one_im, pow_two, Complex.mul_im, zero_sub, neg_ne_zero]
    have hm := mul_ne_zero hz.ne' him
    intro he
    apply hm
    nlinarith

theorem originalEllipticBranch_analyticOnNhd :
    AnalyticOnNhd ℂ (fun z : ℂ => complexEllipticK (1 - z ^ 2)) {z : ℂ | 0 < z.re} := by
  intro z hz
  exact (complexEllipticK_analyticOnNhd (1 - z ^ 2) (rightElliptic_parameter_mem_domain hz)).comp (f := fun z : ℂ => 1 - z ^ 2)
    (show AnalyticAt ℂ (fun z : ℂ => 1 - z ^ 2) z by fun_prop)

theorem halfEllipticIntegral_ofReal {x : ℝ} (hx : 0 < x) :
    halfEllipticIntegral (x : ℂ) = complexEllipticK (1 - (x : ℂ) ^ 2) := by
  rw [← lowerEllipticIntegral_eq_half_right hx, lowerEllipticIntegral_ofReal hx,
    show 1 - (x : ℂ) ^ 2 = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; rfl,
    complexEllipticK_ofReal (by nlinarith : 1 - x ^ 2 < 1)]

/-- The direct continuation agrees with the actual principal elliptic branch throughout
an open half-plane, so its continuation is an interior identity rather than boundary data alone. -/
theorem lowerEllipticIntegral_right_identity {z : ℂ} (hz : 0 < z.re) :
    lowerEllipticIntegral z = complexEllipticK (1 - z ^ 2) := by
  have he := halfEllipticIntegral_analyticOnNhd.eqOn_of_preconnected_of_mem_closure
    originalEllipticBranch_analyticOnNhd (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := (1 : ℂ)) (by simp : (1 : ℂ) ∈ {z : ℂ | 0 < z.re})
  have hclosure : (1 : ℂ) ∈ closure
      ({z : ℂ | halfEllipticIntegral z = complexEllipticK (1 - z ^ 2)} \ {1}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((1 + ε / 2 : ℝ) : ℂ), ⟨halfEllipticIntegral_ofReal (by positivity), ?_⟩, ?_⟩
    · simp only [mem_singleton_iff]
      intro h
      have hreal := congrArg Complex.re h
      simp only [Complex.ofReal_re, Complex.one_re] at hreal
      linarith
    · rw [dist_comm, dist_eq_norm, show ((1 + ε / 2 : ℝ) : ℂ) - 1 = ((ε / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
  rw [lowerEllipticIntegral_eq_half_right hz]
  exact he hclosure hz

theorem lowerEllipticIntegral_differentiableAt_right {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ lowerEllipticIntegral z := by
  apply (halfEllipticIntegral_differentiableAt hz).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
  exact lowerEllipticIntegral_eq_half_right hw

end AperyMoments
