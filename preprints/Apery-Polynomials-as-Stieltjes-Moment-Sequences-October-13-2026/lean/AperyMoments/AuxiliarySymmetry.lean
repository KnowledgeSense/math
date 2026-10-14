import AperyMoments.AuxiliaryHolomorphy

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

def auxiliaryImaginaryReflection (b : ℝ) (z : ℂ) : ℂ :=
  starRingEnd ℂ (continuedAuxiliary b (-starRingEnd ℂ z))

theorem auxiliaryImaginaryReflection_analyticOnNhd {b : ℝ} (hb : 0 < b) :
    AnalyticOnNhd ℂ (auxiliaryImaginaryReflection b) {z : ℂ | z.im < 0} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt Complex.continuous_im continuous_const)
  intro z hz
  have hh : (-starRingEnd ℂ z).im < 0 := by simpa using hz
  have h := ((continuedAuxiliary_analyticOnNhd hb (-starRingEnd ℂ z) hh).differentiableAt.comp
    (starRingEnd ℂ z) (show DifferentiableAt ℂ (fun z : ℂ => -z) (starRingEnd ℂ z) by fun_prop)).conj_conj
  have hd : DifferentiableAt ℂ (auxiliaryImaginaryReflection b) z := by
    unfold auxiliaryImaginaryReflection
    simpa only [Function.comp_def, starRingEnd_apply, star_star] using h
  exact hd.differentiableWithinAt

theorem auxiliaryImaginaryReflection_local {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    {z : ℂ} (hz : z.im < 0) (hball : z ∈ ball (0 : ℂ) b) :
    auxiliaryImaginaryReflection b z = continuedAuxiliary b z := by
  have hh : (-starRingEnd ℂ z).im < 0 := by simpa using hz
  have hconj : starRingEnd ℂ z ∈ ball (0 : ℂ) b := by
    simpa [Metric.mem_ball, dist_eq_norm] using hball
  unfold auxiliaryImaginaryReflection
  rw [← reflectedAuxiliary_lower hh, reflectedAuxiliary_even hb hb2 hconj,
    reflectedAuxiliary_conj]
  simp only [starRingEnd_apply, star_star]
  exact reflectedAuxiliary_lower hz

theorem continuedAuxiliary_imaginary_symmetry {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    {z : ℂ} (hz : z.im < 0) :
    continuedAuxiliary b z = starRingEnd ℂ (continuedAuxiliary b (-starRingEnd ℂ z)) := by
  let z₀ : ℂ := -Complex.I * ((b / 2 : ℝ) : ℂ)
  have hz₀ : z₀.im < 0 := by dsimp [z₀]; simp; linarith
  have hzball : z₀ ∈ ball (0 : ℂ) b := by
    simp only [Metric.mem_ball, dist_zero_right, z₀, norm_mul, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < b / 2)]
    linarith
  have heq : continuedAuxiliary b =ᶠ[𝓝 z₀] auxiliaryImaginaryReflection b := by
    filter_upwards [isOpen_ball.mem_nhds hzball,
      (isOpen_lt Complex.continuous_im continuous_const).mem_nhds hz₀] with w hw hwim
    exact (auxiliaryImaginaryReflection_local hb hb2 hwim hw).symm
  exact (continuedAuxiliary_analyticOnNhd hb).eqOn_of_preconnected_of_eventuallyEq
    (auxiliaryImaginaryReflection_analyticOnNhd hb) (convex_halfSpace_im_lt 0).isPreconnected hz₀ heq hz

/-- The source's reality statement on the entire negative imaginary axis. -/
theorem continuedAuxiliary_negative_imaginary_real {b y : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hy : 0 < y) : (continuedAuxiliary b (-Complex.I * (y : ℂ))).im = 0 := by
  have hz : (-Complex.I * (y : ℂ)).im < 0 := by simpa using neg_neg_of_pos hy
  have h := continuedAuxiliary_imaginary_symmetry hb hb2 hz
  have he : -starRingEnd ℂ (-Complex.I * (y : ℂ)) = -Complex.I * (y : ℂ) := by simp
  rw [he] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

end AperyMoments
