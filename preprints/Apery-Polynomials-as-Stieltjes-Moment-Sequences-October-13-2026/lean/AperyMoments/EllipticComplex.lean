import AperyMoments.EllipticReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
open Set MeasureTheory
namespace AperyMoments

/-- The principal elliptic parameter domain, the complement of the real ray `[1,∞)`. -/
def ellipticDomain : Set ℂ := {z | z.im ≠ 0 ∨ z.re < 1}

/-- The principal complex complete elliptic integral in parameter convention. -/
def complexEllipticK (z : ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..Real.pi / 2,
    (1 - z * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))

theorem elliptic_base_mem_slitPlane {z : ℂ} (hz : z ∈ ellipticDomain) (θ : ℝ) :
    1 - z * (Real.sin θ : ℂ) ^ 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rw [← Complex.ofReal_pow]
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_im,
    Complex.one_im, Complex.mul_im, zero_add, zero_sub]
  rcases hz with hz | hz
  · by_cases hs : Real.sin θ = 0
    · left; simp [hs]
    · right
      exact neg_ne_zero.mpr (mul_ne_zero hz (pow_ne_zero 2 hs))
  · left
    exact ellipticK_base_pos hz θ

theorem complexEllipticK_integrand_continuous {z : ℂ} (hz : z ∈ ellipticDomain) :
    Continuous (fun θ : ℝ => (1 - z * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) :=
  Continuous.cpow (by fun_prop) continuous_const (elliptic_base_mem_slitPlane hz)

theorem complexEllipticK_continuousOn : ContinuousOn complexEllipticK ellipticDomain := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  apply Continuous.cpow (by fun_prop) continuous_const
  intro p
  exact elliptic_base_mem_slitPlane p.1.property p.2

theorem complexEllipticK_ofReal {m : ℝ} (hm : m < 1) :
    complexEllipticK m = (ellipticK m : ℂ) := by
  unfold complexEllipticK ellipticK
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [Complex.ofReal_cpow (ellipticK_base_pos hm θ).le]
  push_cast
  norm_num

def complexEllipticDerivativeIntegrand (z : ℂ) (θ : ℝ) : ℂ :=
  (-(1 / 2 : ℂ)) * (1 - z * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ) - 1) *
    (-(Real.sin θ : ℂ) ^ 2)

theorem complexElliptic_integrand_hasDerivAt {z : ℂ} (hz : z ∈ ellipticDomain) (θ : ℝ) :
    HasDerivAt (fun z : ℂ => (1 - z * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)))
      (complexEllipticDerivativeIntegrand z θ) z := by
  simpa only [complexEllipticDerivativeIntegrand, one_mul, id_eq] using
    (((hasDerivAt_id z).mul_const ((Real.sin θ : ℂ) ^ 2)).const_sub 1).cpow_const
      (c := -(1 / 2 : ℂ)) (elliptic_base_mem_slitPlane hz θ)

theorem complexEllipticDerivativeIntegrand_continuousOn :
    ContinuousOn (fun p : ℂ × ℝ => complexEllipticDerivativeIntegrand p.1 p.2)
      (ellipticDomain ×ˢ univ) := by
  unfold complexEllipticDerivativeIntegrand
  apply ContinuousOn.mul
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.cpow_const (by fun_prop)
    intro p hp
    exact elliptic_base_mem_slitPlane hp.1 p.2
  · fun_prop

theorem ellipticDomain_isOpen : IsOpen ellipticDomain := by
  exact (isOpen_ne_fun Complex.continuous_im continuous_const).union
    (isOpen_lt Complex.continuous_re continuous_const)

theorem complexEllipticDerivativeIntegrand_continuous {z : ℂ} (hz : z ∈ ellipticDomain) :
    Continuous (complexEllipticDerivativeIntegrand z) := by
  unfold complexEllipticDerivativeIntegrand
  apply Continuous.mul
  · apply Continuous.mul continuous_const
    exact Continuous.cpow (by fun_prop) continuous_const (elliptic_base_mem_slitPlane hz)
  · fun_prop


theorem complexEllipticK_differentiableAt {z : ℂ} (hz : z ∈ ellipticDomain) :
    DifferentiableAt ℂ complexEllipticK z := by
  obtain ⟨ε, hε, he⟩ := Metric.isOpen_iff.mp ellipticDomain_isOpen z hz
  have hc : Metric.closedBall z (ε / 2) ⊆ ellipticDomain :=
    (Metric.closedBall_subset_ball (by linarith)).trans he
  have hcompact := (isCompact_closedBall z (ε / 2)).prod (isCompact_Icc : IsCompact (Icc (0:ℝ) (Real.pi/2)))
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    (complexEllipticDerivativeIntegrand_continuousOn.mono (fun p hp => ⟨hc hp.1, mem_univ _⟩))
  have hder := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z θ => (1 - z * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2:ℂ)))
    (F' := complexEllipticDerivativeIntegrand) (μ := volume)
    (bound := fun _ => C) (a := 0) (b := Real.pi / 2)
    (s := Metric.ball z (ε / 2)) (Metric.ball_mem_nhds z (by linarith))
    (by
      filter_upwards [ellipticDomain_isOpen.mem_nhds hz] with w hw
      exact (complexEllipticK_integrand_continuous hw).aestronglyMeasurable)
    ((complexEllipticK_integrand_continuous hz).intervalIntegrable _ _)
    (complexEllipticDerivativeIntegrand_continuous hz).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ hθ w hw => hC (w, θ)
      ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hw).le, by
        rw [uIoc_of_le (by positivity)] at hθ
        exact ⟨hθ.1.le, hθ.2⟩⟩)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun θ _ w hw =>
      complexElliptic_integrand_hasDerivAt (hc (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hw).le)) θ)
  exact hder.2.differentiableAt

theorem complexEllipticK_differentiableOn : DifferentiableOn ℂ complexEllipticK ellipticDomain :=
  fun _ hz => (complexEllipticK_differentiableAt hz).differentiableWithinAt

theorem complexEllipticK_analyticOnNhd : AnalyticOnNhd ℂ complexEllipticK ellipticDomain :=
  complexEllipticK_differentiableOn.analyticOnNhd ellipticDomain_isOpen

end AperyMoments
