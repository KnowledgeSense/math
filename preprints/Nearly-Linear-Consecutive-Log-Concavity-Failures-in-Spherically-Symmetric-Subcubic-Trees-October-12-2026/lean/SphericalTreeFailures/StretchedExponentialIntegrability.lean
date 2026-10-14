import SphericalTreeFailures.CensusFourierDecay
import Mathlib.MeasureTheory.Integral.ExpDecay

set_option backward.isDefEq.respectTransparency false

/-! # Exponential moments of the Fourier envelope -/
namespace SphericalTreeFailures
open MeasureTheory Filter Asymptotics
open scoped Topology

noncomputable def stretchedExponential (c β A t : ℝ) : ℝ :=
  Real.exp (-c * |t| ^ β + A * |t|)

theorem stretchedExponential_continuous {β : ℝ} (hβ : 0 ≤ β) (c A : ℝ) :
    Continuous (stretchedExponential c β A) := by
  unfold stretchedExponential
  exact Real.continuous_exp.comp ((continuous_const.mul ((Real.continuous_rpow_const hβ).comp continuous_abs)).add
    (continuous_const.mul continuous_abs))

theorem stretchedExponential_integrable {c β : ℝ} (hc : 0 < c) (hβ : 1 < β) (A : ℝ) :
    Integrable (stretchedExponential c β A) := by
  have hg : Tendsto (fun x : ℝ => c * x ^ (β - 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < β - 1)).const_mul_atTop hc
  have hb : stretchedExponential c β A =O[atTop] (fun x : ℝ => Real.exp (-1 * x)) := by
    apply IsBigO.of_bound 1
    filter_upwards [hg.eventually (eventually_ge_atTop (A + 1)), eventually_gt_atTop 0] with x hx hx0
    simp only [stretchedExponential, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_pos hx0, one_mul]
    apply Real.exp_le_exp.mpr
    have he : x ^ β = x ^ (β - 1) * x := by
      calc
        x ^ β = x ^ ((β - 1) + 1) := by congr 1; ring
        _ = x ^ (β - 1) * x := by rw [Real.rpow_add hx0, Real.rpow_one]
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hx hx0.le]
  apply (stretchedExponential_continuous (by linarith : 0 ≤ β) c A).locallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant _ hb
      ⟨Set.Ioi 0, Ioi_mem_atTop 0, exp_neg_integrableOn_Ioi 0 (by norm_num)⟩
  exact ae_of_all _ fun x => by simp [Function.comp_def, stretchedExponential]

theorem censusEnvelope_exponential_integrable (p : unitInterval)
    (hc : 1 < 2 * (p : ℝ) ^ 2) (hp1 : (p : ℝ) < 1) (A : ℝ) :
    Integrable (fun t : ℝ => censusEnvelope p t * Real.exp (A * |t|)) := by
  obtain ⟨c, C, hc0, _hC0, hb⟩ := censusEnvelope_stretched_exponential p hc hp1
  have hβ : 1 < fourierExponent (censusScale p) :=
    fourierExponent_gt_one (censusScale_gt_one p hc) (by dsimp [censusScale]; linarith)
  apply ((stretchedExponential_integrable hc0 hβ A).const_mul C).mono'
    (((censusEnvelope_continuous p).mul (Real.continuous_exp.comp (continuous_const.mul continuous_abs))).aestronglyMeasurable)
  apply ae_of_all
  intro t
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (censusEnvelope_nonneg p t) (Real.exp_pos _).le)]
  have h := mul_le_mul_of_nonneg_right (hb t) (Real.exp_pos (A * |t|)).le
  simpa only [stretchedExponential, Real.exp_add, mul_assoc] using h

theorem censusCharacteristic_exponential_integrable (p : unitInterval)
    (hc : 1 < 2 * (p : ℝ) ^ 2) (hp1 : (p : ℝ) < 1) (i : Bool) (A : ℝ) :
    Integrable (fun t : ℝ => ‖censusCharacteristic p i t‖ * Real.exp (A * |t|)) := by
  apply (censusEnvelope_exponential_integrable p hc hp1 A).mono'
    (((censusCharacteristic_continuous p i).norm.mul (Real.continuous_exp.comp (continuous_const.mul continuous_abs))).aestronglyMeasurable)
  apply ae_of_all
  intro t
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem censusCharacteristic_integrable (p : unitInterval)
    (hc : 1 < 2 * (p : ℝ) ^ 2) (hp1 : (p : ℝ) < 1) (i : Bool) :
    Integrable (censusCharacteristic p i) := by
  apply (integrable_norm_iff (censusCharacteristic_continuous p i).aestronglyMeasurable).mp
  simpa using censusCharacteristic_exponential_integrable p hc hp1 i 0

theorem censusCharacteristic_polynomial_exponential_integrable (p : unitInterval)
    (hc : 1 < 2 * (p : ℝ) ^ 2) (hp1 : (p : ℝ) < 1) (i : Bool) (n : ℕ) (A : ℝ) :
    Integrable (fun t : ℝ => |t| ^ n * ‖censusCharacteristic p i t‖ * Real.exp (A * |t|)) := by
  have hint := (censusCharacteristic_exponential_integrable p hc hp1 i (A + 1)).const_mul
    (n.factorial : ℝ)
  have hχ := censusCharacteristic_continuous p i
  apply hint.mono' ((show Continuous (fun t : ℝ => |t| ^ n * ‖censusCharacteristic p i t‖ *
    Real.exp (A * |t|)) by fun_prop).aestronglyMeasurable)
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hp := (div_le_iff₀ hn).mp (Real.pow_div_factorial_le_exp |t| (abs_nonneg _) n)
  have hh := mul_le_mul_of_nonneg_right hp
    (mul_nonneg (norm_nonneg (censusCharacteristic p i t)) (Real.exp_pos (A * |t|)).le)
  convert hh using 1
  · ring
  · rw [add_mul, Real.exp_add, one_mul]
    ring

end SphericalTreeFailures
