import SphericalTreeFailures.CharacteristicConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv

namespace SphericalTreeFailures
open Filter
open scoped Topology

noncomputable def forwardMultiplier (H t : ℝ) : ℂ :=
  (H : ℂ) * (sizeExponential (-1) (t / H) - 1)
noncomputable def backwardMultiplier (H t : ℝ) : ℂ :=
  (H : ℂ) * (1 - sizeExponential 1 (t / H))
noncomputable def secondMultiplier (H t : ℝ) : ℂ := forwardMultiplier H t * backwardMultiplier H t

 theorem secondMultiplier_formula (H t : ℝ) :
    secondMultiplier H t = (H : ℂ) ^ 2 *
      (sizeExponential (-1) (t / H) - 2 + sizeExponential 1 (t / H)) := by
  have he : sizeExponential (-1) (t / H) * sizeExponential 1 (t / H) = 1 := by
    rw [← sizeExponential_add]
    simp [sizeExponential]
  unfold secondMultiplier forwardMultiplier backwardMultiplier
  calc
    _ = (H : ℂ) ^ 2 * (sizeExponential (-1) (t / H) + sizeExponential 1 (t / H) -
        sizeExponential (-1) (t / H) * sizeExponential 1 (t / H) - 1) := by ring
    _ = _ := by rw [he]; ring

theorem forwardMultiplier_norm_le {H : ℝ} (hH : 0 < H) (t : ℝ) :
    ‖forwardMultiplier H t‖ ≤ |t| := by
  have h := sizeExponential_sub_norm_le (-1) 0 (t / H)
  simp only [sizeExponential, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h
  change ‖sizeExponential (-1) (t / H) - 1‖ ≤ _ at h
  norm_num only [sub_zero, abs_neg, abs_one, mul_one] at h
  unfold forwardMultiplier
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  calc
    _ ≤ H * |t / H| := mul_le_mul_of_nonneg_left h hH.le
    _ = _ := by rw [abs_div, abs_of_pos hH]; field_simp

theorem backwardMultiplier_norm_le {H : ℝ} (hH : 0 < H) (t : ℝ) :
    ‖backwardMultiplier H t‖ ≤ |t| := by
  have h := sizeExponential_sub_norm_le 0 1 (t / H)
  simp only [sizeExponential, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h
  change ‖1 - sizeExponential 1 (t / H)‖ ≤ _ at h
  norm_num only [zero_sub, abs_neg, abs_one, mul_one] at h
  unfold backwardMultiplier
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  calc
    _ ≤ H * |t / H| := mul_le_mul_of_nonneg_left h hH.le
    _ = _ := by rw [abs_div, abs_of_pos hH]; field_simp

theorem secondMultiplier_norm_le {H : ℝ} (hH : 0 < H) (t : ℝ) :
    ‖secondMultiplier H t‖ ≤ t ^ 2 := by
  rw [secondMultiplier, norm_mul]
  have h := mul_le_mul (forwardMultiplier_norm_le hH t) (backwardMultiplier_norm_le hH t)
    (norm_nonneg _) (abs_nonneg t)
  simpa only [← pow_two, sq_abs] using h

theorem exponential_difference_limit {γ : ℝ} (hγ : 1 < γ) (c : ℂ) :
    Tendsto (fun m : ℕ => (γ ^ m : ℝ) * (Complex.exp (c / (γ ^ m : ℝ)) - 1))
      atTop (𝓝 c) := by
  have hg : 0 < γ := by linarith
  have hd : HasDerivAt (fun z : ℂ => Complex.exp (c * z)) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul c).cexp
  have hi : Tendsto (fun m : ℕ => (γ ^ m)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
        (inv_nonneg.mpr hg.le) ((inv_lt_one₀ hg).mpr hγ)
    · exact Eventually.of_forall fun m => by simp [ne_of_gt hg]
  have ht := hd.comp_ofReal.tendsto_slope_zero.comp hi
  simpa only [Function.comp_def, zero_add, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    Complex.real_smul, inv_inv, Complex.ofReal_inv, Complex.ofReal_pow, div_eq_mul_inv] using ht

theorem forwardMultiplier_tendsto {γ : ℝ} (hγ : 1 < γ) (t : ℝ) :
    Tendsto (fun m => forwardMultiplier (γ ^ m) t) atTop (𝓝 (-(t : ℂ) * Complex.I)) := by
  have h := exponential_difference_limit hγ (-(t : ℂ) * Complex.I)
  convert h using 1
  funext m
  unfold forwardMultiplier sizeExponential
  push_cast
  congr 2
  ring

theorem backwardMultiplier_tendsto {γ : ℝ} (hγ : 1 < γ) (t : ℝ) :
    Tendsto (fun m => backwardMultiplier (γ ^ m) t) atTop (𝓝 (-(t : ℂ) * Complex.I)) := by
  have h := (exponential_difference_limit hγ ((t : ℂ) * Complex.I)).neg
  convert h using 1
  · funext m
    unfold backwardMultiplier sizeExponential
    push_cast
    have he : (1 : ℂ) * ((t : ℂ) / (γ : ℂ) ^ m * Complex.I) =
        (t : ℂ) * Complex.I / (γ : ℂ) ^ m := by ring
    rw [he]
    ring
  · ring

theorem secondMultiplier_tendsto {γ : ℝ} (hγ : 1 < γ) (t : ℝ) :
    Tendsto (fun m => secondMultiplier (γ ^ m) t) atTop (𝓝 (-(t : ℂ) ^ 2)) := by
  have h := (forwardMultiplier_tendsto hγ t).mul (backwardMultiplier_tendsto hγ t)
  have he : (-(t : ℂ) * Complex.I) * (-(t : ℂ) * Complex.I) = -(t : ℂ) ^ 2 := by
    calc
      _ = (t : ℂ) ^ 2 * Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [he] at h
  exact h

end SphericalTreeFailures
