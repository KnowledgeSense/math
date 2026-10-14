import AperyMoments.SpectralCauchyContinuation

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

theorem upperHalfPlane_nhdsWithin_neBot (x : ℝ) :
    NeBot (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := by
  apply nhdsWithin_neBot.mpr
  intro s hs
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨(x : ℂ) + (ε/2 : ℝ)*Complex.I, hsub ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm]
    simpa [norm_mul, abs_of_pos hε] using (show ε/2 < ε by linarith)
  · simpa using half_pos hε

def spectralCauchyUpperValue (b x : ℝ) : ℂ :=
  limUnder (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (spectralCauchyTransform b)

/-- The lower branch contains the derived spectral-density jump correction. -/
def continuedCauchy (b : ℝ) (z : ℂ) : ℂ :=
  if z.im < 0 then spectralCauchyTransform b z - 2 * Real.pi * Complex.I * continuedAuxiliary b z
  else if 0 < z.im then spectralCauchyTransform b z
  else spectralCauchyUpperValue b z.re

theorem continuedCauchy_upper (b : ℝ) {z : ℂ} (hz : 0 < z.im) :
    continuedCauchy b z = spectralCauchyTransform b z := by
  simp [continuedCauchy, hz, not_lt.mpr hz.le]

theorem continuedCauchy_lower (b : ℝ) {z : ℂ} (hz : z.im < 0) :
    continuedCauchy b z = spectralCauchyTransform b z -
      2 * Real.pi * Complex.I * continuedAuxiliary b z := by
  simp [continuedCauchy, hz]

theorem continuedCauchy_ofReal (b x : ℝ) :
    continuedCauchy b (x : ℂ) = spectralCauchyUpperValue b x := by
  simp [continuedCauchy]

theorem spectralCauchyUpperValue_eq_local {b a r x : ℝ}
    (hA : AnalyticOnNhd ℂ (spectralLocalExtension b a r) (ball (a : ℂ) r))
    (hx : (x : ℂ) ∈ ball (a : ℂ) r) :
    spectralCauchyUpperValue b x = spectralLocalExtension b a r (x : ℂ) := by
  let := upperHalfPlane_nhdsWithin_neBot x
  have hl := (hA (x : ℂ) hx).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := {z : ℂ | 0 < z.im}))
  have he : spectralLocalExtension b a r =ᶠ[𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)]
      spectralCauchyTransform b := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact spectralLocalExtension_upper b a r hz
  exact (hl.congr' he).limUnder_eq

theorem continuedCauchy_eq_local {b a r : ℝ}
    (hA : AnalyticOnNhd ℂ (spectralLocalExtension b a r) (ball (a : ℂ) r)) :
    EqOn (continuedCauchy b) (spectralLocalExtension b a r) (ball (a : ℂ) r) := by
  intro z hz
  rcases lt_trichotomy z.im 0 with hl | he | hu
  · rw [continuedCauchy_lower b hl, spectralLocalExtension_lower b a r hl]
  · have hre : (z.re : ℂ) = z := by apply Complex.ext <;> simp [he]
    rw [← hre, continuedCauchy_ofReal]
    exact spectralCauchyUpperValue_eq_local hA (by simpa [hre] using hz)
  · rw [continuedCauchy_upper b hu, spectralLocalExtension_upper b a r hu]

theorem continuedCauchy_analyticAt_real {b a : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    (ha : |a| < b) : AnalyticAt ℂ (continuedCauchy b) (a : ℂ) := by
  obtain ⟨r, hr, hA⟩ := spectralLocalExtension_exists hb hb2 ha
  apply (hA (a : ℂ) (mem_ball_self hr)).congr
  filter_upwards [ball_mem_nhds (a : ℂ) hr] with z hz
  exact (continuedCauchy_eq_local hA hz).symm

theorem continuedCauchy_differentiableAt_nonreal {b : ℝ} (hb : 0 < b)
    {z : ℂ} (hz : z.im ≠ 0) : DifferentiableAt ℂ (continuedCauchy b) z := by
  have hg := (spectralCauchyTransform_analyticOnNhd hb.le z (Or.inl hz)).differentiableAt
  rcases lt_or_gt_of_ne hz with hz | hz
  · have hH := (continuedAuxiliary_analyticOnNhd hb z hz).differentiableAt
    apply (hg.sub (hH.const_mul (2 * Real.pi * Complex.I))).congr_of_eventuallyEq
    filter_upwards [Complex.continuous_im.continuousAt.eventually (Iio_mem_nhds hz)] with w hw
    exact continuedCauchy_lower b hw
  · apply hg.congr_of_eventuallyEq
    filter_upwards [Complex.continuous_im.continuousAt.eventually (Ioi_mem_nhds hz)] with w hw
    exact continuedCauchy_upper b hw

def continuedCauchyDomain (b : ℝ) : Set ℂ := {z | z.im ≠ 0 ∨ |z.re| < b}

theorem continuedCauchyDomain_isOpen (b : ℝ) : IsOpen (continuedCauchyDomain b) :=
  (isOpen_ne_fun Complex.continuous_im continuous_const).union
    (isOpen_lt Complex.continuous_re.abs continuous_const)

theorem continuedCauchy_analyticOnNhd {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 2) :
    AnalyticOnNhd ℂ (continuedCauchy b) (continuedCauchyDomain b) := by
  apply DifferentiableOn.analyticOnNhd _ (continuedCauchyDomain_isOpen b)
  intro z hz
  by_cases hi : z.im = 0
  · have hre : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
    have ha : |z.re| < b := hz.resolve_left (not_not.mpr hi)
    have hA := continuedCauchy_analyticAt_real hb hb2 ha
    simpa only [hre] using hA.differentiableAt.differentiableWithinAt
  · exact (continuedCauchy_differentiableAt_nonreal hb hi).differentiableWithinAt

end AperyMoments
