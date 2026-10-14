import SphericalTreeFailures.ReleaseDensityIdentification

/-! # Exact entire extensions of the actual conditional, mixture and scaled densities -/
namespace SphericalTreeFailures
open MeasureTheory
open scoped FourierTransform

theorem complexFourierIntegral_charFun_real (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (charFun μ)) (x : ℝ) :
    complexFourierIntegral (charFun μ) 0 x = (characteristicDensity μ x : ℂ) := by
  rw [complexFourierIntegral_zero_eq]
  unfold characteristicDensity
  have h := charFun_fourier_eq_real μ hint (x / (2 * Real.pi))
  rw [← h]
  push_cast
  rfl

theorem censusFourierExtension_real (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (i : Bool) (x : ℝ) :
    censusFourierExtension p i x = (censusDensity p i x : ℂ) := by
  rw [censusFourierExtension_eq, censusDensity_eq_characteristicDensity]
  exact complexFourierIntegral_charFun_real _ (censusCharacteristic_integrable p hc hp1 i) x

noncomputable def censusMixtureFourierExtension (p : unitInterval) (z : ℂ) : ℂ :=
  ((1 - (p : ℝ) : ℝ) : ℂ) * censusFourierExtension p false z +
    (p : ℂ) * censusFourierExtension p true z

theorem censusMixtureFourierExtension_entire (p : unitInterval)
    (hc : 1 < 2 * (p : ℝ) ^ 2) (hp1 : (p : ℝ) < 1) :
    Differentiable ℂ (censusMixtureFourierExtension p) :=
  ((censusFourierExtension_entire p hc hp1 false).const_mul _).add
    ((censusFourierExtension_entire p hc hp1 true).const_mul _)

theorem censusMixtureFourierExtension_real (p : unitInterval)
    (hc : 1 < 2 * (p : ℝ) ^ 2) (hp1 : (p : ℝ) < 1) (x : ℝ) :
    censusMixtureFourierExtension p x = (censusMixtureDensity p x : ℂ) := by
  simp only [censusMixtureFourierExtension, censusFourierExtension_real p hc hp1,
    censusMixtureDensity, Complex.ofReal_add, Complex.ofReal_mul]

theorem censusMixtureDensity_analytic (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (x : ℝ) : AnalyticAt ℝ (censusMixtureDensity p) x :=
  (analyticAt_const.mul (censusDensity_analytic p hc hp1 false x)).add
    (analyticAt_const.mul (censusDensity_analytic p hc hp1 true x))

theorem releaseFourierExtension_real (k : ℕ) (hk : 16384 ≤ k) (x : ℝ) :
    complexFourierIntegral (releaseCharacteristic k hk) 0 x =
      (releaseDensityDerivative k hk 0 x : ℂ) := by
  unfold releaseDensityDerivative
  rw [releaseCharacteristic_eq_charFun, realFourierIntegral_zero_eq]
  apply complexFourierIntegral_charFun_real
  exact charFun_map_mul_integrable _ (censusMixtureCharacteristic_integrable _
    (releaseBroadcast_supercritical k hk) (releaseBroadcast_bounds k hk).2.1)
    (by linarith [release_shift_negative k hk])

end SphericalTreeFailures
