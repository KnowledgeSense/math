import SphericalTreeFailures.LocalLimitKernels

namespace SphericalTreeFailures
open MeasureTheory Filter Set
open scoped Topology

noncomputable def fourierMajorant (c C β t : ℝ) : ℝ :=
  (1 + t ^ 2) * (C * Real.exp (-c * |t| ^ β))

 theorem fourierMajorant_integrable {c β : ℝ} (hc : 0 < c) (hβ : 1 < β) (C : ℝ) :
    Integrable (fourierMajorant c C β) := by
  have h := ((polynomial_stretched_integrable hc hβ 0 0).add
    (polynomial_stretched_integrable hc hβ 2 0)).const_mul C
  convert h using 1
  funext t
  change (1 + t ^ 2) * (C * Real.exp (-c * |t| ^ β)) =
    C * (|t| ^ 0 * Real.exp (-c * |t| ^ β + 0 * |t|) +
      |t| ^ 2 * Real.exp (-c * |t| ^ β + 0 * |t|))
  simp only [pow_zero, zero_mul, add_zero, one_mul, sq_abs]
  ring

theorem limitKernel_integrable (k : ℕ) (hk : 16384 ≤ k) (d : DifferenceKind) (m : ℕ) :
    Integrable (limitKernel k hk d m) := by
  have h := releaseCharacteristic_exponentialFourierIntegrable k hk d.order 0
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  apply h.mono' (limitKernel_measurable k hk d m).aestronglyMeasurable
  apply ae_of_all
  intro t
  unfold limitKernel limitMultiplier
  rw [norm_mul, norm_pow, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, releaseCharacteristic_norm_parity]

theorem finiteLimitKernel_bound (k : ℕ) (hk : 16384 ≤ k) (d : DifferenceKind) (m : ℕ)
    {c C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t : ℝ, |t| ≤ Real.pi * fluctuationScale (releaseParameter k hk) ^ m →
      scaledEnvelope m k (releaseParameter k hk) t ≤ C * Real.exp
        (-c * |t| ^ fourierExponent (fluctuationScale (releaseParameter k hk)))) (t : ℝ) :
    ‖finiteLimitKernel k hk d m t‖ ≤
      fourierMajorant c C (fourierExponent (fluctuationScale (releaseParameter k hk))) t := by
  have hg : 0 < fluctuationScale (releaseParameter k hk) ^ m :=
    pow_pos (by have := release_scale_gt_one k hk; linarith) _
  by_cases ht : t ∈ releaseFrequencyWindow k hk m
  · rw [finiteLimitKernel, indicator_of_mem ht, norm_mul]
    exact mul_le_mul (differenceMultiplier_norm_bound d hg t)
      ((finiteReleaseCharacteristic_norm_le k hk m t).trans (hb t (abs_le.mpr ht)))
      (norm_nonneg _) (by positivity)
  · rw [finiteLimitKernel, indicator_of_notMem ht, norm_zero]
    dsimp [fourierMajorant]
    positivity

theorem limitKernel_bound (k : ℕ) (hk : 16384 ≤ k) (d : DifferenceKind) (m : ℕ)
    {c C : ℝ}
    (hb : ∀ t : ℝ, ‖releaseCharacteristic k hk t‖ ≤ C * Real.exp
      (-c * |t| ^ fourierExponent (fluctuationScale (releaseParameter k hk)))) (t : ℝ) :
    ‖limitKernel k hk d m t‖ ≤
      fourierMajorant c C (fourierExponent (fluctuationScale (releaseParameter k hk))) t := by
  rw [limitKernel, norm_mul, releaseCharacteristic_norm_parity]
  exact mul_le_mul (limitMultiplier_norm_bound d t) (hb t) (norm_nonneg _) (by positivity)

theorem localLimitKernel_L1_tendsto (k : ℕ) (hk : 16384 ≤ k) (d : DifferenceKind) :
    Tendsto (fun m => ∫ t, ‖finiteLimitKernel k hk d m t - limitKernel k hk d m t‖)
      atTop (𝓝 0) := by
  obtain ⟨c₀, C₀, hc₀, _, hb₀⟩ := release_limit_fourier_decay k hk
  obtain ⟨c₁, C₁, hc₁, hC₁, h, hb₁⟩ := release_uniform_fourier_decay k hk
  have hβ := fourierExponent_gt_one (release_scale_gt_one k hk)
    (fluctuationScale_bounds hk (releaseParameter_spec k hk).1).2.1
  apply kernel_L1_convergence
    (Eventually.of_forall fun m => (finiteLimitKernel_integrable k hk d m).aestronglyMeasurable)
    (Eventually.of_forall fun m => (limitKernel_measurable k hk d m).aestronglyMeasurable)
    ((fourierMajorant_integrable hc₁ hβ C₁).add (fourierMajorant_integrable hc₀ hβ C₀))
  · filter_upwards [eventually_ge_atTop h] with m hm
    exact ae_of_all _ fun t => (norm_sub_le _ _).trans (add_le_add
      (finiteLimitKernel_bound k hk d m hC₁.le (hb₁ m hm) t) (limitKernel_bound k hk d m hb₀ t))
  · exact ae_of_all _ fun t => localLimitKernel_pointwise k hk d t

end SphericalTreeFailures
