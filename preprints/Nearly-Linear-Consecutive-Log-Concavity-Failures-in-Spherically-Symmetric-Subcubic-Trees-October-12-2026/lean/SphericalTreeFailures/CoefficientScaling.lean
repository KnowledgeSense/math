import SphericalTreeFailures.DifferenceFourierIntegral

namespace SphericalTreeFailures
open MeasureTheory Set

noncomputable def releaseScale (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) : ℝ :=
  fluctuationScale (releaseParameter k hk) ^ m
noncomputable def releaseCenter (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) : ℝ :=
  totalCenter (releaseBroadcastParameter k hk) k m (tunedActivity (releaseParameter k hk))
noncomputable def releaseMass (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) (j : ℤ) : ℝ :=
  graphLatticeMass m k (tunedActivity (releaseParameter k hk)) (tunedActivity_pos (releaseParameter_pos k hk)) j
noncomputable def releaseGrid (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) (j : ℤ) : ℝ :=
  ((j : ℝ) - releaseCenter k hk m) / releaseScale k hk m

noncomputable def scaledMassDifference (d : DifferenceKind) (H : ℝ) (w : ℤ → ℝ) (j : ℤ) : ℝ :=
  match d with
  | .value => H * w j
  | .forward => H ^ 2 * (w (j + 1) - w j)
  | .backward => H ^ 2 * (w j - w (j - 1))
  | .second => H ^ 3 * (w (j + 1) - 2 * w j + w (j - 1))

 theorem releaseScale_pos (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) : 0 < releaseScale k hk m :=
  pow_pos (by have := release_scale_gt_one k hk; linarith) _

theorem releaseGrid_succ (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) (j : ℤ) :
    releaseGrid k hk m (j + 1) = releaseGrid k hk m j + 1 / releaseScale k hk m := by
  unfold releaseGrid
  push_cast
  ring

theorem releaseGrid_pred (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) (j : ℤ) :
    releaseGrid k hk m (j - 1) = releaseGrid k hk m j - 1 / releaseScale k hk m := by
  unfold releaseGrid
  push_cast
  ring

theorem value_kernel_inversion (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) (j : ℤ) :
    fourierEvaluation (finiteLimitKernel k hk .value m) (releaseGrid k hk m j) =
      ((2 * Real.pi : ℝ) : ℂ) * ((releaseScale k hk m * releaseMass k hk m j : ℝ) : ℂ) := by
  have hH := releaseScale_pos k hk m
  have he : (fun t => sizeExponential (-releaseGrid k hk m j) t * finiteLimitKernel k hk .value m t) =
      (releaseFrequencyWindow k hk m).indicator
        (fun t => sizeExponential (-releaseGrid k hk m j) t * finiteReleaseCharacteristic k hk m t) := by
    funext t
    by_cases ht : t ∈ releaseFrequencyWindow k hk m <;>
      simp [finiteLimitKernel, differenceMultiplier, ht]
  unfold fourierEvaluation
  rw [he, integral_indicator (show MeasurableSet (releaseFrequencyWindow k hk m) from measurableSet_Icc)]
  change (∫ t in Icc (- (Real.pi * releaseScale k hk m)) (Real.pi * releaseScale k hk m),
    sizeExponential (-releaseGrid k hk m j) t * finiteReleaseCharacteristic k hk m t) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by have := mul_pos Real.pi_pos hH; linarith :
    -(Real.pi * releaseScale k hk m) ≤ Real.pi * releaseScale k hk m)]
  have h := graphLatticeMass_scaled_inversion m k (tunedActivity (releaseParameter k hk))
    (tunedActivity_pos (releaseParameter_pos k hk)) (releaseCenter k hk m) (releaseScale k hk m) hH.ne' j
  simpa only [releaseGrid, neg_div, releaseMass, finiteReleaseCharacteristic, releaseCenter,
    releaseScale] using h

theorem difference_kernel_inversion (k : ℕ) (hk : 16384 ≤ k) (d : DifferenceKind) (m : ℕ) (j : ℤ) :
    fourierEvaluation (finiteLimitKernel k hk d m) (releaseGrid k hk m j) =
      ((2 * Real.pi : ℝ) : ℂ) * (scaledMassDifference d (releaseScale k hk m) (releaseMass k hk m) j : ℂ) := by
  cases d
  · exact value_kernel_inversion k hk m j
  · unfold fourierEvaluation
    simp_rw [finiteLimitKernel_mul_value k hk .forward m]
    unfold differenceMultiplier
    rw [forward_fourierEvaluation (finiteLimitKernel_integrable k hk .value m)]
    simp only [show fluctuationScale (releaseParameter k hk) ^ m = releaseScale k hk m from rfl]
    rw [← releaseGrid_succ, value_kernel_inversion, value_kernel_inversion]
    unfold scaledMassDifference
    push_cast
    ring
  · unfold fourierEvaluation
    simp_rw [finiteLimitKernel_mul_value k hk .backward m]
    unfold differenceMultiplier
    rw [backward_fourierEvaluation (finiteLimitKernel_integrable k hk .value m)]
    simp only [show fluctuationScale (releaseParameter k hk) ^ m = releaseScale k hk m from rfl]
    rw [← releaseGrid_pred, value_kernel_inversion, value_kernel_inversion]
    unfold scaledMassDifference
    push_cast
    ring
  · unfold fourierEvaluation
    simp_rw [finiteLimitKernel_mul_value k hk .second m]
    unfold differenceMultiplier
    rw [second_fourierEvaluation (finiteLimitKernel_integrable k hk .value m)]
    simp only [show fluctuationScale (releaseParameter k hk) ^ m = releaseScale k hk m from rfl]
    rw [← releaseGrid_succ, ← releaseGrid_pred, value_kernel_inversion, value_kernel_inversion,
      value_kernel_inversion]
    unfold scaledMassDifference
    push_cast
    ring

end SphericalTreeFailures
