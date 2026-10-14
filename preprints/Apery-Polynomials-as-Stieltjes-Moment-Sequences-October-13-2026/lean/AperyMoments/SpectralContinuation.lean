import AperyMoments.LatticeContinuation
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def latticeContinuationDomain : Set ℂ := {z | z.im < 0 ∨ 0 < z.re}

theorem latticeContinuationDomain_isOpen : IsOpen latticeContinuationDomain :=
  (isOpen_lt Complex.continuous_im continuous_const).union
    (isOpen_lt continuous_const Complex.continuous_re)

theorem continuedLattice_analyticOnNhd_domain :
    AnalyticOnNhd ℂ continuedLattice latticeContinuationDomain := by
  apply DifferentiableOn.analyticOnNhd _ latticeContinuationDomain_isOpen
  intro z hz
  rcases hz with hz | hz
  · exact (continuedLattice_analyticOnNhd z hz).differentiableAt.differentiableWithinAt
  · have hd : 0 < (z / 4).re := by simpa using div_pos hz (by norm_num : (0 : ℝ) < 4)
    exact (((lowerEllipticIntegral_differentiableAt_right hd).comp z
      (show DifferentiableAt ℂ (fun z : ℂ => z / 4) z by fun_prop)).div_const _).differentiableWithinAt

/-- The actual continued arcsine convolution in angular coordinates. -/
def continuedSpectral (b : ℝ) (w : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, continuedLattice (w - (b * Real.cos θ : ℝ))

def spectralContinuationDomain (b : ℝ) : Set ℂ := {w | w.im < 0 ∨ b < w.re}

theorem spectralContinuationDomain_isOpen (b : ℝ) : IsOpen (spectralContinuationDomain b) :=
  (isOpen_lt Complex.continuous_im continuous_const).union
    (isOpen_lt continuous_const Complex.continuous_re)

theorem continuedSpectral_shift_mem {b : ℝ} (hb : 0 ≤ b) {w : ℂ}
    (hw : w ∈ spectralContinuationDomain b) (θ : ℝ) :
    w - (b * Real.cos θ : ℝ) ∈ latticeContinuationDomain := by
  rcases hw with hw | hw
  · left
    simpa using hw
  · right
    simp only [Complex.sub_re, Complex.ofReal_re]
    nlinarith [mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hb]

theorem continuedSpectral_integrand_continuous {b : ℝ} (hb : 0 ≤ b) {w : ℂ}
    (hw : w ∈ spectralContinuationDomain b) :
    Continuous (fun θ : ℝ => continuedLattice (w - (b * Real.cos θ : ℝ))) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  exact (continuedLattice_analyticOnNhd_domain _ (continuedSpectral_shift_mem hb hw θ)).continuousAt.comp (f := fun θ : ℝ => w - (b * Real.cos θ : ℝ))
    (show ContinuousAt (fun θ : ℝ => w - (b * Real.cos θ : ℝ)) θ by fun_prop)

theorem continuedSpectral_derivative_continuousOn {b : ℝ} (hb : 0 ≤ b) :
    ContinuousOn (fun p : ℂ × ℝ => deriv continuedLattice (p.1 - (b * Real.cos p.2 : ℝ)))
      (spectralContinuationDomain b ×ˢ univ) := by
  apply continuedLattice_analyticOnNhd_domain.deriv.continuousOn.comp (by fun_prop)
  intro p hp
  exact continuedSpectral_shift_mem hb hp.1 p.2

theorem continuedSpectral_derivative_continuous {b : ℝ} (hb : 0 ≤ b) {w : ℂ}
    (hw : w ∈ spectralContinuationDomain b) :
    Continuous (fun θ : ℝ => deriv continuedLattice (w - (b * Real.cos θ : ℝ))) := by
  have h := (continuedSpectral_derivative_continuousOn hb).comp
    (show ContinuousOn (fun θ : ℝ => (w, θ)) univ by fun_prop)
    (fun _ _ => ⟨hw, mem_univ _⟩)
  exact continuousOn_univ.mp h

theorem continuedSpectral_integrand_hasDerivAt {b : ℝ} (hb : 0 ≤ b) {w : ℂ}
    (hw : w ∈ spectralContinuationDomain b) (θ : ℝ) :
    HasDerivAt (fun w : ℂ => continuedLattice (w - (b * Real.cos θ : ℝ)))
      (deriv continuedLattice (w - (b * Real.cos θ : ℝ))) w := by
  simpa only [Function.comp_def, mul_one, id_eq] using ((continuedLattice_analyticOnNhd_domain _ (continuedSpectral_shift_mem hb hw θ)).differentiableAt.hasDerivAt).comp w
    ((hasDerivAt_id w).sub_const ((b * Real.cos θ : ℝ) : ℂ))

theorem continuedSpectral_differentiableAt {b : ℝ} (hb : 0 ≤ b) {w : ℂ}
    (hw : w ∈ spectralContinuationDomain b) : DifferentiableAt ℂ (continuedSpectral b) w := by
  obtain ⟨ε, hε, he⟩ := Metric.isOpen_iff.mp (spectralContinuationDomain_isOpen b) w hw
  have hc : Metric.closedBall w (ε / 2) ⊆ spectralContinuationDomain b :=
    (Metric.closedBall_subset_ball (by linarith)).trans he
  have hcompact := (isCompact_closedBall w (ε / 2)).prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) Real.pi))
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    ((continuedSpectral_derivative_continuousOn hb).mono (fun p hp => ⟨hc hp.1, mem_univ _⟩))
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w θ => continuedLattice (w - (b * Real.cos θ : ℝ)))
    (F' := fun w θ => deriv continuedLattice (w - (b * Real.cos θ : ℝ))) (μ := volume)
    (bound := fun _ => C) (a := 0) (b := Real.pi)
    (s := Metric.ball w (ε / 2)) (Metric.ball_mem_nhds w (by linarith))
    (by
      filter_upwards [(spectralContinuationDomain_isOpen b).mem_nhds hw] with z hz
      exact (continuedSpectral_integrand_continuous hb hz).aestronglyMeasurable)
    ((continuedSpectral_integrand_continuous hb hw).intervalIntegrable _ _)
    (continuedSpectral_derivative_continuous hb hw).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ hθ z hz => hC (z, θ)
      ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hz).le, by
        rw [uIoc_of_le Real.pi_pos.le] at hθ
        exact ⟨hθ.1.le, hθ.2⟩⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ z hz => continuedSpectral_integrand_hasDerivAt hb
      (hc (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hz).le)) θ)
  exact hd.2.differentiableAt.const_mul _

theorem continuedSpectral_analyticOnNhd {b : ℝ} (hb : 0 ≤ b) :
    AnalyticOnNhd ℂ (continuedSpectral b) (spectralContinuationDomain b) := by
  apply DifferentiableOn.analyticOnNhd _ (spectralContinuationDomain_isOpen b)
  intro w hw
  exact (continuedSpectral_differentiableAt hb hw).differentiableWithinAt

theorem continuedSpectral_ofReal {b w : ℝ} (hb : 0 ≤ b) (hw : b < w) :
    continuedSpectral b (w : ℂ) = (continuedDensity b w : ℂ) := by
  unfold continuedSpectral continuedDensity
  have he θ : continuedLattice ((w : ℂ) - (b * Real.cos θ : ℝ)) =
      (latticeExpression (w - b * Real.cos θ) : ℂ) := by
    rw [← Complex.ofReal_sub]
    exact continuedLattice_ofReal (by nlinarith [mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hb])
  simp_rw [he]
  rw [intervalIntegral.integral_ofReal]
  push_cast
  rfl

theorem continuedSpectral_positive_boundary {b w : ℝ} (hb : 0 ≤ b) (hw : b < w) :
    Filter.Tendsto (continuedSpectral b) (nhdsWithin (w : ℂ) {z : ℂ | z.im < 0})
      (nhds (continuedDensity b w : ℂ)) := by
  rw [← continuedSpectral_ofReal hb hw]
  exact (continuedSpectral_differentiableAt hb (Or.inr hw)).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds

end AperyMoments
