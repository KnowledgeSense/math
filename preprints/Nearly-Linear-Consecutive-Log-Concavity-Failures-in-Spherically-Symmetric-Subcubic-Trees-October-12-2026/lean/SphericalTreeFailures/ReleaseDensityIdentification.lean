import SphericalTreeFailures.DensityNonconcavity
import SphericalTreeFailures.ReleaseDensityDerivatives

/-! # Identification, positivity and non-log-concavity of the release density -/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory

theorem releaseBroadcast_bounds (k : ℕ) (hk : 16384 ≤ k) :
    99 / 100 < (releaseBroadcastParameter k hk : ℝ) ∧
      (releaseBroadcastParameter k hk : ℝ) < 1 ∧
      1 - (releaseBroadcastParameter k hk : ℝ) < 1 / 8192 := by
  obtain ⟨hb,h0,h1⟩ := broadcastParameter_bounds hk (releaseParameter_spec k hk).1
  refine ⟨h0,h1,?_⟩
  have hk' : (16384 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < (k : ℝ) + 2 := by positivity
  have hb' := (div_lt_iff₀ hden).mp hb
  change 1 - broadcastParameter (releaseParameter k hk) < 1 / 8192
  nlinarith

theorem releaseCharacteristic_eq_charFun (k : ℕ) (hk : 16384 ≤ k) :
    releaseCharacteristic k hk = charFun ((censusMixtureLaw (releaseBroadcastParameter k hk)).map
      (fun x : ℝ => tailShift k (releaseParameter k hk) * x)) := by
  funext t
  simp only [charFun_map_mul]
  rfl

theorem releaseDensityDerivative_zero_eq (k : ℕ) (hk : 16384 ≤ k) (x : ℝ) :
    releaseDensityDerivative k hk 0 x = |(tailShift k (releaseParameter k hk))⁻¹| *
      censusMixtureDensity (releaseBroadcastParameter k hk) (x / tailShift k (releaseParameter k hk)) := by
  unfold releaseDensityDerivative
  rw [releaseCharacteristic_eq_charFun, realFourierIntegral_zero_eq,
    characteristicDensity_map_mul _ (by linarith [release_shift_negative k hk]),
    ← censusMixtureDensity_eq_characteristicDensity _ (releaseBroadcast_supercritical k hk)
      (releaseBroadcast_bounds k hk).2.1]

theorem releaseDensityDerivative_zero_pos (k : ℕ) (hk : 16384 ≤ k) (x : ℝ) :
    0 < releaseDensityDerivative k hk 0 x := by
  rw [releaseDensityDerivative_zero_eq]
  exact mul_pos (abs_pos.mpr (inv_ne_zero (by linarith [release_shift_negative k hk])))
    (censusMixtureDensity_pos _ (releaseBroadcast_supercritical k hk) (releaseBroadcast_bounds k hk).2.1 _)

theorem releaseDensityDerivative_analytic (k : ℕ) (hk : 16384 ≤ k) (n : ℕ) (x : ℝ) :
    AnalyticAt ℝ (releaseDensityDerivative k hk n) x :=
  ((complexFourierIntegral_entire (releaseCharacteristic_continuous k hk)
    (releaseCharacteristic_exponentialFourierIntegrable k hk) n).analyticAt x).re_ofReal

theorem releaseLimitLaw_eq_withDensity (k : ℕ) (hk : 16384 ≤ k) :
    (censusMixtureLaw (releaseBroadcastParameter k hk)).map
      (fun x : ℝ => tailShift k (releaseParameter k hk) * x) =
      volume.withDensity (fun x => ENNReal.ofReal (releaseDensityDerivative k hk 0 x)) := by
  have hint : Integrable (charFun ((censusMixtureLaw (releaseBroadcastParameter k hk)).map
      (fun x : ℝ => tailShift k (releaseParameter k hk) * x))) := by
    exact charFun_map_mul_integrable _ (censusMixtureCharacteristic_integrable _
      (releaseBroadcast_supercritical k hk) (releaseBroadcast_bounds k hk).2.1)
      (by linarith [release_shift_negative k hk])
  rw [measure_eq_withDensity_characteristicDensity _ hint]
  congr 1
  funext x
  congr 1
  unfold releaseDensityDerivative
  rw [releaseCharacteristic_eq_charFun, realFourierIntegral_zero_eq]

theorem concave_log_of_scaled {f g : ℝ → ℝ} (hf : ∀ x, 0 < f x) {c A : ℝ}
    (hc : c ≠ 0) (hA : 0 < A) (he : ∀ x, g x = A * f (x / c))
    (hconc : ConcaveOn ℝ Set.univ (fun x => Real.log (g x))) :
    ConcaveOn ℝ Set.univ (fun x => Real.log (f x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := hconc.2 (Set.mem_univ (c * x)) (Set.mem_univ (c * y)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have hx : c * x / c = x := by field_simp
  have hy : c * y / c = y := by field_simp
  have hz : (a * (c * x) + b * (c * y)) / c = a * x + b * y := by field_simp
  rw [he, he, he, hx, hy, hz,
    Real.log_mul (ne_of_gt hA) (ne_of_gt (hf x)),
    Real.log_mul (ne_of_gt hA) (ne_of_gt (hf y)),
    Real.log_mul (ne_of_gt hA) (ne_of_gt (hf _))] at h
  nlinarith only [h, congrArg (fun u : ℝ => u * Real.log A) hab]

theorem releaseDensityDerivative_not_log_concave (k : ℕ) (hk : 16384 ≤ k) :
    ¬ ConcaveOn ℝ Set.univ (fun x => Real.log (releaseDensityDerivative k hk 0 x)) := by
  intro h
  have hb := releaseBroadcast_bounds k hk
  apply censusMixtureDensity_not_log_concave _ hb.1 hb.2.1 hb.2.2
  exact concave_log_of_scaled
    (censusMixtureDensity_pos _ (releaseBroadcast_supercritical k hk) hb.2.1)
    (by linarith [release_shift_negative k hk])
    (abs_pos.mpr (inv_ne_zero (by linarith [release_shift_negative k hk])))
    (releaseDensityDerivative_zero_eq k hk) h

end SphericalTreeFailures
