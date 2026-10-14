import SphericalTreeFailures.DifferenceKernelIdentities
import SphericalTreeFailures.LocalLimitDomination

namespace SphericalTreeFailures
open MeasureTheory

noncomputable def fourierEvaluation (K : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t, sizeExponential (-x) t * K t

 theorem forward_fourierEvaluation {K : ℝ → ℂ} (hK : Integrable K) (x H : ℝ) :
    (∫ t, sizeExponential (-x) t * (forwardMultiplier H t * K t)) =
      (H : ℂ) * (fourierEvaluation K (x + 1 / H) - fourierEvaluation K x) := by
  have he (t : ℝ) : sizeExponential (-x) t * (forwardMultiplier H t * K t) =
      (H : ℂ) * (sizeExponential (-(x + 1 / H)) t * K t - sizeExponential (-x) t * K t) := by
    rw [← mul_assoc, forward_kernel_identity]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_sub (integrable_fourier_kernel hK _) (integrable_fourier_kernel hK _)]
  rfl

theorem backward_fourierEvaluation {K : ℝ → ℂ} (hK : Integrable K) (x H : ℝ) :
    (∫ t, sizeExponential (-x) t * (backwardMultiplier H t * K t)) =
      (H : ℂ) * (fourierEvaluation K x - fourierEvaluation K (x - 1 / H)) := by
  have he (t : ℝ) : sizeExponential (-x) t * (backwardMultiplier H t * K t) =
      (H : ℂ) * (sizeExponential (-x) t * K t - sizeExponential (-(x - 1 / H)) t * K t) := by
    rw [← mul_assoc, backward_kernel_identity]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_sub (integrable_fourier_kernel hK _) (integrable_fourier_kernel hK _)]
  rfl

theorem second_fourierEvaluation {K : ℝ → ℂ} (hK : Integrable K) (x H : ℝ) :
    (∫ t, sizeExponential (-x) t * (secondMultiplier H t * K t)) =
      (H : ℂ) ^ 2 * (fourierEvaluation K (x + 1 / H) - 2 * fourierEvaluation K x +
        fourierEvaluation K (x - 1 / H)) := by
  have he (t : ℝ) : sizeExponential (-x) t * (secondMultiplier H t * K t) =
      (H : ℂ) ^ 2 * ((sizeExponential (-(x + 1 / H)) t * K t -
        2 * (sizeExponential (-x) t * K t)) + sizeExponential (-(x - 1 / H)) t * K t) := by
    rw [← mul_assoc, second_kernel_identity]
    ring
  simp_rw [he]
  have hsub : Integrable (fun t => sizeExponential (-(x + 1 / H)) t * K t -
      2 * (sizeExponential (-x) t * K t)) :=
    (integrable_fourier_kernel hK _).sub ((integrable_fourier_kernel hK _).const_mul 2)
  have hmul : Integrable (fun t => 2 * (sizeExponential (-x) t * K t)) :=
    (integrable_fourier_kernel hK _).const_mul 2
  rw [integral_const_mul, integral_add hsub (integrable_fourier_kernel hK _),
    integral_sub (integrable_fourier_kernel hK _) hmul, integral_const_mul]
  rfl

theorem finiteLimitKernel_mul_value (k : ℕ) (hk : 16384 ≤ k) (d : DifferenceKind) (m : ℕ) (t : ℝ) :
    finiteLimitKernel k hk d m t = differenceMultiplier d (fluctuationScale (releaseParameter k hk) ^ m) t *
      finiteLimitKernel k hk .value m t := by
  unfold finiteLimitKernel
  by_cases ht : t ∈ releaseFrequencyWindow k hk m <;> simp [ht, differenceMultiplier]

end SphericalTreeFailures
