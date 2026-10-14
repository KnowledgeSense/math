import SphericalTreeFailures.ReleaseCharacteristic
import SphericalTreeFailures.FiniteAnnulus
import SphericalTreeFailures.EntireFourierIntegral

namespace SphericalTreeFailures
open MeasureTheory

 theorem releaseCharacteristic_norm_le_one (k : ℕ) (hk : 16384 ≤ k) (t : ℝ) :
    ‖releaseCharacteristic k hk t‖ ≤ 1 := norm_charFun_le_one _

theorem releaseCharacteristic_continuous (k : ℕ) (hk : 16384 ≤ k) :
    Continuous (releaseCharacteristic k hk) :=
  continuous_charFun.comp (continuous_const.mul continuous_id)

theorem releaseCharacteristic_norm_neg (k : ℕ) (hk : 16384 ≤ k) (t : ℝ) :
    ‖releaseCharacteristic k hk (-t)‖ = ‖releaseCharacteristic k hk t‖ := by
  unfold releaseCharacteristic censusMixtureCharacteristic
  rw [mul_neg, charFun_neg]
  exact Complex.norm_conj _

theorem releaseCharacteristic_norm_parity (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) (t : ℝ) :
    ‖releaseCharacteristic k hk ((-1 : ℝ) ^ m * t)‖ = ‖releaseCharacteristic k hk t‖ := by
  rcases neg_one_pow_eq_or (R := ℝ) m with h | h
  · rw [h, one_mul]
  · rw [h, neg_one_mul, releaseCharacteristic_norm_neg]

theorem release_limit_fourier_decay (k : ℕ) (hk : 16384 ≤ k) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ,
      ‖releaseCharacteristic k hk t‖ ≤ C * Real.exp
        (-c * |t| ^ fourierExponent (fluctuationScale (releaseParameter k hk))) := by
  let p := releaseBroadcastParameter k hk
  let r := releaseParameter k hk
  let κ := tailShift k r
  let β := fourierExponent (fluctuationScale r)
  have hp1 : (p : ℝ) < 1 := (broadcastParameter_bounds hk (releaseParameter_spec k hk).1).2.2
  obtain ⟨c, C, hc, hC, hb⟩ := censusEnvelope_stretched_exponential p
    (releaseBroadcast_supercritical k hk) hp1
  have hκ : 0 < |κ| := abs_pos.mpr (by have := release_shift_negative k hk; dsimp [κ, r]; linarith)
  refine ⟨c * |κ| ^ β, C, mul_pos hc (Real.rpow_pos_of_pos hκ _), hC, ?_⟩
  intro t
  have h := (censusMixtureCharacteristic_norm_le p (κ * t)).trans (hb (κ * t))
  have he : |κ * t| ^ β = |κ| ^ β * |t| ^ β := by
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  change ‖releaseCharacteristic k hk t‖ ≤ C * Real.exp (-c * |κ * t| ^ β) at h
  rw [he] at h
  convert h using 1
  congr 2
  ring

theorem polynomial_stretched_integrable {c β : ℝ} (hc : 0 < c) (hβ : 1 < β) (n : ℕ) (A : ℝ) :
    Integrable (fun t : ℝ => |t| ^ n * Real.exp (-c * |t| ^ β + A * |t|)) := by
  have hint := (stretchedExponential_integrable hc hβ (A + 1)).const_mul (n.factorial : ℝ)
  apply hint.mono' ((show Continuous (fun t : ℝ => |t| ^ n * Real.exp (-c * |t| ^ β + A * |t|)) from
    (continuous_abs.pow n).mul (stretchedExponential_continuous (by linarith) c A)).aestronglyMeasurable)
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hp := (div_le_iff₀ hn).mp (Real.pow_div_factorial_le_exp |t| (abs_nonneg _) n)
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-c * |t| ^ β + A * |t|)).le
  convert hh using 1
  dsimp [stretchedExponential]
  rw [show -c * |t| ^ β + (A + 1) * |t| = |t| + (-c * |t| ^ β + A * |t|) by ring,
    Real.exp_add]
  ring

theorem releaseCharacteristic_exponentialFourierIntegrable (k : ℕ) (hk : 16384 ≤ k) :
    ExponentialFourierIntegrable (releaseCharacteristic k hk) := by
  obtain ⟨c, C, hc, hC, hb⟩ := release_limit_fourier_decay k hk
  have hg := release_scale_gt_one k hk
  have hg2 := (fluctuationScale_bounds hk (releaseParameter_spec k hk).1).2.1
  have hβ := fourierExponent_gt_one hg hg2
  intro n A
  apply ((polynomial_stretched_integrable hc hβ n A).const_mul C).mono'
    ((show Continuous (fun t : ℝ => |t| ^ n * ‖releaseCharacteristic k hk t‖ * Real.exp (A * |t|)) by
      exact ((continuous_abs.pow n).mul (releaseCharacteristic_continuous k hk).norm).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_abs))).aestronglyMeasurable)
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb t) (by positivity : 0 ≤ |t| ^ n))
    (Real.exp_pos (A * |t|)).le
  convert h using 1
  rw [Real.exp_add]
  ring

end SphericalTreeFailures
