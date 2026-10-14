import AperyMoments

example (n : ℕ) {α : ℝ} (hα : α ≠ 0) :
    AperyMoments.reciprocalPolynomial n α = α ^ n * AperyMoments.aperyPolynomial n α⁻¹ :=
  AperyMoments.reciprocalPolynomial_eq n hα

example {α : ℝ} (hα : 0 ≤ α) (s : ℝ) : 0 ≤ AperyMoments.candidateDensity α s :=
  AperyMoments.candidateDensity_nonneg hα s

example : AnalyticOnNhd ℂ AperyMoments.lowerEllipticIntegral {z : ℂ | z.im < 0} :=
  AperyMoments.lowerEllipticIntegral_analyticOnNhd

example {x : ℝ} (hx : 0 < x) (hx4 : x < 4) :=
  AperyMoments.continuedLattice_negative_boundary hx hx4

example {z : ℂ} (hz : 0 < z.re) :=
  AperyMoments.lowerEllipticIntegral_right_identity hz

example {b y : ℝ} (hb : 0 < b) (hb2 : b ≤ 2) (hy : 0 < y) :
    (AperyMoments.continuedAuxiliary b (-Complex.I * (y : ℂ))).im = 0 :=
  AperyMoments.continuedAuxiliary_negative_imaginary_real hb hb2 hy

example {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 2) :
    DifferentiableOn ℂ (AperyMoments.reflectedAuxiliary b) (Metric.ball (0 : ℂ) b) :=
  AperyMoments.reflectedAuxiliary_differentiableOn hb hb2

example {b : ℝ} (hb : 0 ≤ b) : (∫ w : ℝ, AperyMoments.spectralDensity b w) = 1 :=
  AperyMoments.spectralDensity_integral hb

example {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    AnalyticOnNhd ℂ (AperyMoments.momentTransform α) AperyMoments.momentTransformDomain :=
  AperyMoments.momentTransform_analyticOnNhd hα hα1

example : AperyMoments.HasPositiveMomentRepresentation 1 :=
  AperyMoments.positive_moments_for_full_parameter_ray 1 le_rfl

example : AperyMoments.HasPositiveMomentRepresentation 2 :=
  AperyMoments.positive_moments_for_full_parameter_ray 2 (by norm_num)

example (x : ℝ) (hx : 1 ≤ x) : AperyMoments.HasPositiveMomentRepresentation x :=
  AperyMoments.positive_moments_for_full_parameter_ray x hx

example {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    (∫ t : ℝ, t ^ n ∂AperyMoments.reciprocalMomentMeasure α) =
      AperyMoments.reciprocalPolynomial n α :=
  (AperyMoments.reciprocalMomentMeasure_moments hα hα1 n).2

example : AperyMoments.aperyPolynomial 2 1 = 73 := by
  norm_num [AperyMoments.aperyPolynomial, Finset.sum_range_succ, Nat.choose]
