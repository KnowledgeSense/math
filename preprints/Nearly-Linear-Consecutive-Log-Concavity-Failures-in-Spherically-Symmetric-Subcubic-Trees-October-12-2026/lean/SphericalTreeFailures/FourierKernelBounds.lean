import SphericalTreeFailures.CharacteristicConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option backward.isDefEq.respectTransparency false

namespace SphericalTreeFailures
open MeasureTheory Filter
open scoped Topology

 theorem integrable_fourier_kernel {K : ℝ → ℂ} (hK : Integrable K) (x : ℝ) :
    Integrable (fun t => sizeExponential (-x) t * K t) := by
  apply hK.norm.mono' ((by unfold sizeExponential; fun_prop : Measurable (fun t : ℝ => sizeExponential (-x) t)).aestronglyMeasurable.mul
    hK.aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    change ‖sizeExponential (-x) t * K t‖ ≤ ‖K t‖
    rw [norm_mul, sizeExponential_norm, one_mul]

theorem fourier_kernel_difference_bound {K L : ℝ → ℂ} (hK : Integrable K) (hL : Integrable L) (x : ℝ) :
    ‖(∫ t, sizeExponential (-x) t * K t) - ∫ t, sizeExponential (-x) t * L t‖ ≤
      ∫ t, ‖K t - L t‖ := by
  rw [← integral_sub (integrable_fourier_kernel hK x) (integrable_fourier_kernel hL x)]
  apply norm_integral_le_of_norm_le (hK.sub hL).norm
  exact Eventually.of_forall fun t => by rw [← mul_sub, norm_mul, sizeExponential_norm, one_mul]; rfl

theorem fourier_kernel_uniform_of_L1 {K L : ℕ → ℝ → ℂ}
    (hK : ∀ m, Integrable (K m)) (hL : ∀ m, Integrable (L m))
    (hconv : Tendsto (fun m => ∫ t, ‖K m t - L m t‖) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ x : ℝ,
      ‖(∫ t, sizeExponential (-x) t * K m t) - ∫ t, sizeExponential (-x) t * L m t‖ < ε := by
  filter_upwards [hconv.eventually (gt_mem_nhds hε)] with m hm
  exact fun x => (fourier_kernel_difference_bound (hK m) (hL m) x).trans_lt hm

theorem kernel_L1_convergence {K L : ℕ → ℝ → ℂ} {B : ℝ → ℝ}
    (hK : ∀ᶠ m in atTop, AEStronglyMeasurable (K m))
    (hL : ∀ᶠ m in atTop, AEStronglyMeasurable (L m))
    (hB : Integrable B)
    (hb : ∀ᶠ m in atTop, ∀ᵐ t, ‖K m t - L m t‖ ≤ B t)
    (hc : ∀ᵐ t, Tendsto (fun m => K m t - L m t) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ t, ‖K m t - L m t‖) atTop (𝓝 0) := by
  have ht := tendsto_integral_filter_of_dominated_convergence
    (F := fun m t => ‖K m t - L m t‖) (f := fun _ : ℝ => (0 : ℝ)) B
    (by filter_upwards [hK, hL] with m hm hn; exact (hm.sub hn).norm)
    (by filter_upwards [hb] with m hm; simpa only [Real.norm_eq_abs, abs_norm] using hm)
    hB (by filter_upwards [hc] with t ht; simpa only [norm_zero] using ht.norm)
  simpa using ht

end SphericalTreeFailures
