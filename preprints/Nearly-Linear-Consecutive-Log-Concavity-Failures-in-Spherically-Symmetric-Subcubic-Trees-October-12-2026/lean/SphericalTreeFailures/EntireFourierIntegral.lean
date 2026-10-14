import SphericalTreeFailures.CensusFourierExtension

/-! # Differentiating exponentially integrable inverse Fourier transforms -/
namespace SphericalTreeFailures
open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable def complexFourierIntegral (φ : ℝ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t : ℝ, (-(t : ℂ) * Complex.I) ^ n * inverseFourierKernel t z * φ t

def ExponentialFourierIntegrable (φ : ℝ → ℂ) : Prop :=
  ∀ n : ℕ, ∀ A : ℝ, Integrable (fun t : ℝ => |t| ^ n * ‖φ t‖ * Real.exp (A * |t|))

theorem complexFourierIntegral_integrable {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hint : ExponentialFourierIntegrable φ) (n : ℕ) (z : ℂ) :
    Integrable (fun t : ℝ => (-(t : ℂ) * Complex.I) ^ n * inverseFourierKernel t z * φ t) := by
  apply (hint n ‖z‖).mono'
    ((show Continuous (fun t : ℝ => (-(t : ℂ) * Complex.I) ^ n * inverseFourierKernel t z * φ t) by
      unfold inverseFourierKernel; fun_prop).aestronglyMeasurable)
  apply ae_of_all
  intro t
  simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one]
  have h := mul_le_mul_of_nonneg_left (inverseFourierKernel_norm_le t z)
    (pow_nonneg (abs_nonneg t) n)
  have h' := mul_le_mul_of_nonneg_right h (norm_nonneg (φ t))
  convert h' using 1
  rw [mul_comm ‖z‖ |t|]
  ring

theorem complexFourierIntegral_hasDerivAt {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hint : ExponentialFourierIntegrable φ) (n : ℕ) (z : ℂ) :
    HasDerivAt (complexFourierIntegral φ n) (complexFourierIntegral φ (n + 1) z) z := by
  let F : ℂ → ℝ → ℂ := fun w t => (-(t : ℂ) * Complex.I) ^ n * inverseFourierKernel t w * φ t
  let F' : ℂ → ℝ → ℂ := fun w t => (-(t : ℂ) * Complex.I) ^ (n + 1) * inverseFourierKernel t w * φ t
  let B : ℝ → ℝ := fun t => |t| ^ (n + 1) * ‖φ t‖ * Real.exp ((‖z‖ + 1) * |t|)
  have hB : Integrable B := hint (n + 1) (‖z‖ + 1)
  have hd (t : ℝ) (w : ℂ) : HasDerivAt (fun w => F w t) (F' w t) w := by
    have h := ((inverseFourierKernel_hasDerivAt t w).const_mul ((-(t : ℂ) * Complex.I) ^ n)).mul_const (φ t)
    convert h using 1
    dsimp [F']
    rw [pow_succ]
    ring
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := B) (μ := volume) (x₀ := z)
    (s := Metric.ball z 1) (Metric.ball_mem_nhds z (by norm_num))
    (Eventually.of_forall fun w => (show Continuous (F w) by dsimp [F, inverseFourierKernel]; fun_prop).aestronglyMeasurable)
    (complexFourierIntegral_integrable hφ hint n z)
    (show AEStronglyMeasurable (F' z) volume from
      (show Continuous (F' z) by dsimp [F', inverseFourierKernel]; fun_prop).aestronglyMeasurable)
    (ae_of_all _ fun t w hw => ?_) hB (ae_of_all _ fun t w _ => hd t w)
  · exact hderiv.2.const_mul _
  · have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      have hh := norm_le_insert z w
      have hdist : ‖z - w‖ < 1 := by simpa only [dist_eq_norm, norm_sub_rev] using Metric.mem_ball.mp hw
      linarith
    dsimp [F', B]
    simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one]
    have he := (inverseFourierKernel_norm_le t w).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw' (abs_nonneg t)))
    have hmul := mul_le_mul_of_nonneg_left he (pow_nonneg (abs_nonneg t) (n + 1))
    have hmul' := mul_le_mul_of_nonneg_right hmul (norm_nonneg (φ t))
    convert hmul' using 1
    rw [mul_comm (‖z‖ + 1) |t|]
    ring

theorem complexFourierIntegral_entire {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hint : ExponentialFourierIntegrable φ) (n : ℕ) :
    Differentiable ℂ (complexFourierIntegral φ n) :=
  fun z => (complexFourierIntegral_hasDerivAt hφ hint n z).differentiableAt

theorem complexFourierIntegral_hasDerivAt_real {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hint : ExponentialFourierIntegrable φ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => complexFourierIntegral φ n y) (complexFourierIntegral φ (n + 1) x) x := by
  exact (complexFourierIntegral_hasDerivAt hφ hint n x).comp_ofReal

noncomputable def realFourierIntegral (φ : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℝ :=
  (complexFourierIntegral φ n x).re

theorem realFourierIntegral_hasDerivAt {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hint : ExponentialFourierIntegrable φ) (n : ℕ) (x : ℝ) :
    HasDerivAt (realFourierIntegral φ n) (realFourierIntegral φ (n + 1) x) x := by
  exact (complexFourierIntegral_hasDerivAt hφ hint n x).real_of_complex

theorem censusCharacteristic_exponentialFourierIntegrable (p : unitInterval)
    (hc : 1 < 2 * (p : ℝ) ^ 2) (hp1 : (p : ℝ) < 1) (i : Bool) :
    ExponentialFourierIntegrable (censusCharacteristic p i) :=
  censusCharacteristic_polynomial_exponential_integrable p hc hp1 i

theorem censusFourierExtension_eq (p : unitInterval) (i : Bool) :
    censusFourierExtension p i = complexFourierIntegral (censusCharacteristic p i) 0 := by
  funext z
  simp [censusFourierExtension, complexFourierIntegral]

end SphericalTreeFailures
