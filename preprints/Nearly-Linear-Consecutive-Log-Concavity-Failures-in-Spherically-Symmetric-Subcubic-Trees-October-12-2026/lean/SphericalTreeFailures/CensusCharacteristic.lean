import SphericalTreeFailures.CensusFixedPoint
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! # Characteristic functions of the actual census limit -/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexConjugate

noncomputable def censusCharacteristic (p : unitInterval) (i : Bool) (t : ℝ) : ℂ :=
  charFun (censusLimitLaw p i) t

noncomputable def censusMixtureCharacteristic (p : unitInterval) (t : ℝ) : ℂ :=
  charFun (censusMixtureLaw p) t

noncomputable def censusEnvelope (p : unitInterval) (t : ℝ) : ℝ :=
  max ‖censusCharacteristic p false t‖ ‖censusCharacteristic p true t‖

instance censusMixtureLaw_probability (p : unitInterval) : IsProbabilityMeasure (censusMixtureLaw p) := by
  constructor
  simp only [censusMixtureLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr p.property.2) p.property.1]
  simp

instance descendantLaw_probability (p : unitInterval) (i : Bool) :
    IsProbabilityMeasure (descendantLaw p i) := by
  cases i <;> dsimp [descendantLaw] <;> infer_instance

theorem integrable_probability_exponential (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun x : ℝ => Complex.exp ((t : ℂ) * x * Complex.I)) μ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  exact ae_of_all _ fun x => by simp [Complex.norm_exp]

theorem censusMixtureCharacteristic_eq (p : unitInterval) (t : ℝ) :
    censusMixtureCharacteristic p t =
      ((1 - (p : ℝ) : ℝ) : ℂ) * censusCharacteristic p false t +
      (p : ℂ) * censusCharacteristic p true t := by
  unfold censusMixtureCharacteristic censusCharacteristic censusMixtureLaw
  simp only [charFun_apply_real]
  rw [integral_add_measure]
  · simp only [integral_smul_measure, ENNReal.toReal_ofReal (sub_nonneg.mpr p.property.2),
      ENNReal.toReal_ofReal p.property.1, Complex.real_smul]
  · exact (integrable_probability_exponential _ t).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_probability_exponential _ t).smul_measure ENNReal.ofReal_ne_top

theorem charFun_scaled_sum (μ : Measure ℝ) [IsProbabilityMeasure μ] (c t : ℝ) :
    charFun ((μ.prod μ).map (fun z : ℝ × ℝ => c * (z.1 + z.2))) t =
      charFun μ (c * t) ^ 2 := by
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  have he (x y : ℝ) :
      Complex.exp ((t : ℂ) * ((c * (x + y) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((c * t : ℝ) : ℂ) * x * Complex.I) *
          Complex.exp (((c * t : ℝ) : ℂ) * y * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [integral_prod_mul (fun x : ℝ => Complex.exp (((c * t : ℝ) : ℂ) * x * Complex.I))
    (fun x : ℝ => Complex.exp (((c * t : ℝ) : ℂ) * x * Complex.I))]
  simp only [charFun_apply_real, pow_two]

theorem censusCharacteristic_fixedPoint (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (i : Bool) (t : ℝ) :
    censusCharacteristic p i t = charFun (descendantLaw p i) (-t / censusScale p) ^ 2 := by
  unfold censusCharacteristic
  rw [censusLimitLaw_fixedPoint p hc i]
  have he : (fun z : ℝ × ℝ => -(z.1 + z.2) / censusScale p) =
      (fun z : ℝ × ℝ => (-(censusScale p)⁻¹) * (z.1 + z.2)) := by
    funext z
    ring
  rw [he, charFun_scaled_sum]
  congr 2
  ring

theorem censusCharacteristic_fixedPoint_one (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (t : ℝ) :
    censusCharacteristic p true t = censusCharacteristic p false (-t / censusScale p) ^ 2 :=
  censusCharacteristic_fixedPoint p hc true t

theorem censusCharacteristic_fixedPoint_zero (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (t : ℝ) :
    censusCharacteristic p false t =
      (((1 - (p : ℝ) : ℝ) : ℂ) * censusCharacteristic p false (-t / censusScale p) +
      (p : ℂ) * censusCharacteristic p true (-t / censusScale p)) ^ 2 := by
  rw [censusCharacteristic_fixedPoint p hc false]
  exact congrArg (fun z : ℂ => z ^ 2) (censusMixtureCharacteristic_eq p _)

theorem censusCharacteristic_norm_le_one (p : unitInterval) (i : Bool) (t : ℝ) :
    ‖censusCharacteristic p i t‖ ≤ 1 := norm_charFun_le_one t

theorem censusCharacteristic_neg (p : unitInterval) (i : Bool) (t : ℝ) :
    censusCharacteristic p i (-t) = conj (censusCharacteristic p i t) := charFun_neg t

theorem censusCharacteristic_norm_neg (p : unitInterval) (i : Bool) (t : ℝ) :
    ‖censusCharacteristic p i (-t)‖ = ‖censusCharacteristic p i t‖ := by
  rw [censusCharacteristic_neg, Complex.norm_conj]

theorem censusEnvelope_nonneg (p : unitInterval) (t : ℝ) : 0 ≤ censusEnvelope p t :=
  (norm_nonneg _).trans (le_max_left _ _)

theorem censusEnvelope_le_one (p : unitInterval) (t : ℝ) : censusEnvelope p t ≤ 1 :=
  max_le (censusCharacteristic_norm_le_one p false t) (censusCharacteristic_norm_le_one p true t)

theorem censusEnvelope_neg (p : unitInterval) (t : ℝ) : censusEnvelope p (-t) = censusEnvelope p t := by
  simp only [censusEnvelope, censusCharacteristic_norm_neg]

theorem censusMixtureCharacteristic_norm_le (p : unitInterval) (t : ℝ) :
    ‖censusMixtureCharacteristic p t‖ ≤ censusEnvelope p t := by
  rw [censusMixtureCharacteristic_eq]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr p.property.2), abs_of_nonneg p.property.1]
  have h0 := mul_le_mul_of_nonneg_left (le_max_left
    ‖censusCharacteristic p false t‖ ‖censusCharacteristic p true t‖)
      (sub_nonneg.mpr p.property.2)
  have h1 := mul_le_mul_of_nonneg_left (le_max_right
    ‖censusCharacteristic p false t‖ ‖censusCharacteristic p true t‖) p.property.1
  unfold censusEnvelope
  nlinarith

theorem censusEnvelope_square (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (t : ℝ) :
    censusEnvelope p t ≤ censusEnvelope p (t / censusScale p) ^ 2 := by
  unfold censusEnvelope
  apply max_le
  · rw [censusCharacteristic_fixedPoint p hc false, norm_pow]
    have h := censusMixtureCharacteristic_norm_le p (-t / censusScale p)
    change ‖censusMixtureCharacteristic p (-t / censusScale p)‖ ^ 2 ≤ _
    rw [neg_div, censusEnvelope_neg] at h
    simpa only [neg_div, censusEnvelope] using pow_le_pow_left₀ (norm_nonneg _) h 2
  · rw [censusCharacteristic_fixedPoint_one p hc, norm_pow, neg_div,
      censusCharacteristic_norm_neg]
    exact pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) 2

end SphericalTreeFailures
