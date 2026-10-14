import AperyMoments.PositiveMomentMeasure

namespace AperyMoments

/-- Every real parameter on the full source ray has one compactly supported
nonnegative probability measure representing all original Apéry polynomials. -/
theorem positive_moments_for_full_parameter_ray (x : ℝ) (hx : 1 ≤ x) :
    HasPositiveMomentRepresentation x :=
  apery_positive_moment_representation hx

end AperyMoments
