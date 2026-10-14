import SphericalTreeFailures.CoefficientScaling

namespace SphericalTreeFailures
open MeasureTheory Filter
open scoped Topology

noncomputable def parityCharacteristic (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) (t : ℝ) : ℂ :=
  releaseCharacteristic k hk ((-1 : ℝ) ^ m * t)

 theorem limitKernel_fourierIntegral (k : ℕ) (hk : 16384 ≤ k) (d : DifferenceKind) (m : ℕ) (x : ℝ) :
    complexFourierIntegral (parityCharacteristic k hk m) d.order x =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * fourierEvaluation (limitKernel k hk d m) x := by
  unfold complexFourierIntegral fourierEvaluation
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    unfold inverseFourierKernel sizeExponential limitKernel limitMultiplier parityCharacteristic
    have he : -(t : ℂ) * (x : ℂ) * Complex.I = (-x : ℝ) * ((t : ℂ) * Complex.I) := by
      push_cast
      ring
    dsimp only
    rw [he]
    ring

theorem local_limit_error_bound (k : ℕ) (hk : 16384 ≤ k) (d : DifferenceKind) (m : ℕ) (j : ℤ) :
    |scaledMassDifference d (releaseScale k hk m) (releaseMass k hk m) j -
      realFourierIntegral (parityCharacteristic k hk m) d.order (releaseGrid k hk m j)| ≤
        (2 * Real.pi)⁻¹ * ∫ t, ‖finiteLimitKernel k hk d m t - limitKernel k hk d m t‖ := by
  let a := scaledMassDifference d (releaseScale k hk m) (releaseMass k hk m) j
  let z := complexFourierIntegral (parityCharacteristic k hk m) d.order (releaseGrid k hk m j)
  have he : (a : ℂ) - z = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (fourierEvaluation (finiteLimitKernel k hk d m) (releaseGrid k hk m j) -
        fourierEvaluation (limitKernel k hk d m) (releaseGrid k hk m j)) := by
    dsimp [a, z]
    rw [difference_kernel_inversion, limitKernel_fourierIntegral]
    have hp : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 : ℝ) * Real.pi ≠ 0)
    field_simp
  have h := fourier_kernel_difference_bound (finiteLimitKernel_integrable k hk d m)
    (limitKernel_integrable k hk d m) (releaseGrid k hk m j)
  calc
    _ = |((a : ℂ) - z).re| := by simp [a, z, realFourierIntegral]
    _ ≤ ‖(a : ℂ) - z‖ := Complex.abs_re_le_norm _
    _ = (2 * Real.pi)⁻¹ * ‖fourierEvaluation (finiteLimitKernel k hk d m) (releaseGrid k hk m j) -
        fourierEvaluation (limitKernel k hk d m) (releaseGrid k hk m j)‖ := by
      rw [he, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

theorem local_limit_uniform (k : ℕ) (hk : 16384 ≤ k) (d : DifferenceKind)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ j : ℤ,
      |scaledMassDifference d (releaseScale k hk m) (releaseMass k hk m) j -
        realFourierIntegral (parityCharacteristic k hk m) d.order (releaseGrid k hk m j)| < ε := by
  have he : 0 < ε * (2 * Real.pi) := by positivity
  filter_upwards [(localLimitKernel_L1_tendsto k hk d).eventually (gt_mem_nhds he)] with m hm
  intro j
  apply (local_limit_error_bound k hk d m j).trans_lt
  have hp : 0 < (2 * Real.pi)⁻¹ := by positivity
  have h := mul_lt_mul_of_pos_left hm hp
  simpa only [← mul_assoc, inv_mul_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0), one_mul,
    mul_comm ε (2 * Real.pi)] using h

end SphericalTreeFailures
