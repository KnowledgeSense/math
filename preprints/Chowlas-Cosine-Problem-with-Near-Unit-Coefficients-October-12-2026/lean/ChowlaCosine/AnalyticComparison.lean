import ChowlaCosine.BedertPointwise
import ChowlaCosine.ConvolutionFourier

namespace ChowlaCosine
open MeasureTheory AddCircle
open scoped ComplexConjugate

theorem continuous_realConvolve {f g : Circle → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (realConvolve f g) := by
  exact (HasCompactSupport.of_compactSpace g).continuous_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable hg

theorem norm_convolve_le_realConvolve (g : C(Circle, ℂ)) (x : Circle) :
    ‖convolve g g x‖ ≤ realConvolve (fun y => ‖g y‖) (fun y => ‖g y‖) x := by
  simpa only [convolve, realConvolve, norm_mul] using
    norm_integral_le_integral_norm (fun y : Circle => g y * g (x-y))

/-- A pointwise majorant transfers to the convolution pairing. -/
theorem convolution_pairing_comparison (g : C(Circle, ℂ))
    (φ ψ : C(Circle, ℝ)) (M : ℝ)
    (hmajor : ∀ x, |φ x| ≤ ψ x + M) :
    ‖∫ x, (φ x : ℂ) * star (convolve g g x) ∂haarAddCircle‖ ≤
      ∫ x, (ψ x + M) *
        realConvolve (fun y => ‖g y‖) (fun y => ‖g y‖) x ∂haarAddCircle := by
  have hc : Continuous (convolve g g) :=
    (HasCompactSupport.of_compactSpace (g : Circle → ℂ)).continuous_convolution_right
      (ContinuousLinearMap.mul ℂ ℂ) g.continuous.locallyIntegrable g.continuous
  have hr := continuous_realConvolve g.continuous.norm g.continuous.norm
  have hi := ((Complex.continuous_ofReal.comp φ.continuous).mul hc.star).norm
  have hj : Continuous (fun x => (ψ x + M) * realConvolve (fun y => ‖g y‖) (fun y => ‖g y‖) x) := (ψ.continuous.add continuous_const).mul hr
  calc
    _ ≤ ∫ x, ‖(φ x : ℂ) * star (convolve g g x)‖ ∂haarAddCircle :=
      norm_integral_le_integral_norm _
    _ ≤ _ := by
      apply integral_mono
        (hi.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (hj.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      intro x
      change ‖(φ x : ℂ) * star (convolve g g x)‖ ≤ _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_star]
      exact mul_le_mul (hmajor x) (norm_convolve_le_realConvolve g x)
        (norm_nonneg _) (le_trans (abs_nonneg _) (hmajor x))

end ChowlaCosine
