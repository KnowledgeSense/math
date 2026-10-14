import SphericalTreeFailures.FourierReflection

namespace SphericalTreeFailures
open MeasureTheory

noncomputable def releaseDensityDerivative (k : ℕ) (hk : 16384 ≤ k) (n : ℕ) : ℝ → ℝ :=
  realFourierIntegral (releaseCharacteristic k hk) n

theorem releaseDensityDerivative_hasDerivAt (k : ℕ) (hk : 16384 ≤ k) (n : ℕ) (x : ℝ) :
    HasDerivAt (releaseDensityDerivative k hk n) (releaseDensityDerivative k hk (n + 1) x) x :=
  realFourierIntegral_hasDerivAt (releaseCharacteristic_continuous k hk)
    (releaseCharacteristic_exponentialFourierIntegrable k hk) n x

theorem releaseDensityDerivative_continuous (k : ℕ) (hk : 16384 ≤ k) (n : ℕ) :
    Continuous (releaseDensityDerivative k hk n) :=
  continuous_iff_continuousAt.mpr fun x => (releaseDensityDerivative_hasDerivAt k hk n x).continuousAt

theorem realFourierIntegral_bound (φ : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    |realFourierIntegral φ n x| ≤ (2 * Real.pi)⁻¹ * ∫ t : ℝ, |t| ^ n * ‖φ t‖ := by
  unfold realFourierIntegral complexFourierIntegral
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    simp [norm_pow, inverseFourierKernel_norm]

theorem releaseDensityDerivative_bounded (k : ℕ) (hk : 16384 ≤ k) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, |releaseDensityDerivative k hk n x| ≤ B := by
  refine ⟨(2 * Real.pi)⁻¹ * ∫ t : ℝ, |t| ^ n * ‖releaseCharacteristic k hk t‖, ?_, ?_⟩
  · exact mul_nonneg (by positivity) (integral_nonneg fun t => by positivity)
  · exact realFourierIntegral_bound _ n

end SphericalTreeFailures
