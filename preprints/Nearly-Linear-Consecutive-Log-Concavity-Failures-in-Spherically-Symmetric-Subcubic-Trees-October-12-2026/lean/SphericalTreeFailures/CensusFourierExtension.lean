import SphericalTreeFailures.StretchedExponentialIntegrability
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # The entire inverse Fourier integral of the actual census law -/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

noncomputable def inverseFourierKernel (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(t : ℂ) * z * Complex.I)

noncomputable def censusFourierExtension (p : unitInterval) (i : Bool) (z : ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, inverseFourierKernel t z * censusCharacteristic p i t

theorem inverseFourierKernel_norm (t : ℝ) (z : ℂ) :
    ‖inverseFourierKernel t z‖ = Real.exp (t * z.im) := by
  simp [inverseFourierKernel, Complex.norm_exp]

theorem inverseFourierKernel_norm_le (t : ℝ) (z : ℂ) :
    ‖inverseFourierKernel t z‖ ≤ Real.exp (|t| * ‖z‖) := by
  rw [inverseFourierKernel_norm]
  apply Real.exp_le_exp.mpr
  calc
    t * z.im ≤ |t * z.im| := le_abs_self _
    _ = |t| * |z.im| := abs_mul _ _
    _ ≤ |t| * ‖z‖ := mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (abs_nonneg _)

theorem censusFourierExtension_integrable (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (i : Bool) (z : ℂ) :
    Integrable (fun t : ℝ => inverseFourierKernel t z * censusCharacteristic p i t) := by
  have hχ := censusCharacteristic_continuous p i
  apply (censusCharacteristic_exponential_integrable p hc hp1 i ‖z‖).mono'
    ((show Continuous (fun t : ℝ => inverseFourierKernel t z * censusCharacteristic p i t) by
      unfold inverseFourierKernel; fun_prop).aestronglyMeasurable)
  apply ae_of_all
  intro t
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (inverseFourierKernel_norm_le t z) (norm_nonneg _)).trans_eq
    (by rw [mul_comm |t| ‖z‖, mul_comm])

theorem inverseFourierKernel_hasDerivAt (t : ℝ) (z : ℂ) :
    HasDerivAt (inverseFourierKernel t) (-(t : ℂ) * Complex.I * inverseFourierKernel t z) z := by
  have h := (((hasDerivAt_id z).const_mul (-(t : ℂ))).mul_const Complex.I).cexp
  change HasDerivAt (fun w : ℂ => Complex.exp (-(t : ℂ) * w * Complex.I))
    (-(t : ℂ) * Complex.I * Complex.exp (-(t : ℂ) * z * Complex.I)) z
  simpa only [id_eq, mul_one, mul_comm, mul_left_comm, mul_assoc] using h

theorem censusFourierExtension_hasDerivAt (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (i : Bool) (z : ℂ) :
    HasDerivAt (censusFourierExtension p i)
      (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ, (-(t : ℂ) * Complex.I) * inverseFourierKernel t z * censusCharacteristic p i t) z := by
  have hχ := censusCharacteristic_continuous p i
  let F : ℂ → ℝ → ℂ := fun w t => inverseFourierKernel t w * censusCharacteristic p i t
  let F' : ℂ → ℝ → ℂ := fun w t =>
    (-(t : ℂ) * Complex.I) * inverseFourierKernel t w * censusCharacteristic p i t
  let B : ℝ → ℝ := fun t => |t| * ‖censusCharacteristic p i t‖ * Real.exp ((‖z‖ + 1) * |t|)
  have hB : Integrable B := by
    simpa only [pow_one] using censusCharacteristic_polynomial_exponential_integrable
      p hc hp1 i 1 (‖z‖ + 1)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := B) (μ := volume) (x₀ := z)
    (s := Metric.ball z 1) (Metric.ball_mem_nhds z (by norm_num))
    (Eventually.of_forall fun w => (show Continuous (F w) by dsimp [F, inverseFourierKernel]; fun_prop).aestronglyMeasurable)
    (censusFourierExtension_integrable p hc hp1 i z)
    (show AEStronglyMeasurable (F' z) volume from
      (show Continuous (F' z) by dsimp [F', inverseFourierKernel]; fun_prop).aestronglyMeasurable)
    (ae_of_all _ fun t w hw => ?_) hB
    (ae_of_all _ fun t w _ => (inverseFourierKernel_hasDerivAt t w).mul_const (censusCharacteristic p i t))
  · exact hderiv.2.const_mul _
  · have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      have hh := norm_le_insert z w
      have hd : ‖z - w‖ < 1 := by simpa only [dist_eq_norm, norm_sub_rev] using (Metric.mem_ball.mp hw)
      linarith
    dsimp [F', B]
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    have he := (inverseFourierKernel_norm_le t w).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw' (abs_nonneg t)))
    have hmul := mul_le_mul_of_nonneg_left he (abs_nonneg t)
    have hmul' := mul_le_mul_of_nonneg_right hmul (norm_nonneg (censusCharacteristic p i t))
    convert hmul' using 1
    rw [mul_comm (‖z‖ + 1) |t|]
    ring

/-- The complex inverse transform is entire. The measure-density identification is separate. -/
theorem censusFourierExtension_entire (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (i : Bool) : Differentiable ℂ (censusFourierExtension p i) :=
  fun z => (censusFourierExtension_hasDerivAt p hc hp1 i z).differentiableAt

end SphericalTreeFailures
