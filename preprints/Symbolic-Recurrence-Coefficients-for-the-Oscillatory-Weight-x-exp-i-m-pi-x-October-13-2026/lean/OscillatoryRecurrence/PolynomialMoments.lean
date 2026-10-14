import OscillatoryRecurrence.Moments
import Mathlib.Algebra.Polynomial.Eval.Defs

noncomputable section
open Polynomial
namespace OscillatoryRecurrence

lemma endpoint_parity_term (t : ℂ) (n : ℕ) :
    (if Even n then (2 : ℂ)*(-1)^(n/2) else 0) * (-t^2)^(n/2) =
      (1+(-1 : ℂ)^n)*(-t)^n := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have he : (-1 : ℂ)^(k*2) = 1 := by rw [Nat.mul_comm k 2, pow_mul]; norm_num
    simp [pow_mul]
    ring_nf
    rw [he]
    ring
  · simp [pow_add, pow_mul]

lemma endpointMoment_eval_recurrence (t : ℂ) (r : ℕ) :
    (endpointMoment (r+1)).eval₂ (Rat.castHom ℂ) (-t^2) =
      (r+2)*(endpointMoment r).eval₂ (Rat.castHom ℂ) (-t^2) +
        (1+(-1 : ℂ)^(r+1))*(-t)^(r+1) := by
  rw [endpointMoment]
  simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  have h : (Rat.castHom ℂ) (if Even (r+1) then 2*(-1 : ℚ)^((r+1)/2) else 0) =
      (if Even (r+1) then (2 : ℂ)*(-1)^((r+1)/2) else 0) := by
    split_ifs <;> simp
  rw [h, endpoint_parity_term]
  norm_cast

lemma exponentialMoment_polynomial (t s : ℂ) (ht : t ≠ 0)
    (hplus : Complex.exp t = s) (hminus : Complex.exp (-t) = s) (r : ℕ) :
    t^(r+1) * exponentialMoment t (r+1) =
      s*(-1)^r*(endpointMoment r).eval₂ (Rat.castHom ℂ) (-t^2) := by
  induction r with
  | zero =>
    have hz : exponentialMoment t 0 = 0 := by rw [exponentialMoment_zero t ht, hplus, hminus]; simp
    have h := exponentialMoment_recurrence t 0
    simpa [hplus,hminus,hz,endpointMoment, mul_two] using h
  | succ r ih =>
    have h := exponentialMoment_recurrence t (r+1)
    rw [hplus,hminus] at h
    rw [endpointMoment_eval_recurrence]
    have hh := congrArg (fun a : ℂ => t^(r+1)*a) h
    have hi := congrArg (fun a : ℂ => (r+2)*a) ih
    have hsign : ((-1 : ℂ)^r)^2 = 1 := by rw [← pow_mul, Nat.mul_comm r 2, pow_mul]; norm_num
    simp only [Nat.cast_add, Nat.cast_one] at hh
    rw [neg_pow t (r+1)]
    simp only [pow_succ] at hh hi ⊢
    linear_combination hh - hi - (t^r*t*s*(1-(-1)^r))*hsign

lemma integral_frequency_exp (m : ℤ) :
    Complex.exp (Complex.I*((m : ℝ)*Real.pi)) = (-1 : ℂ)^m := by
  have he : Complex.I*((m : ℝ)*Real.pi) = (m : ℂ)*((Real.pi : ℂ)*Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_int_mul, Complex.exp_pi_mul_I]

lemma integral_frequency_exp_neg (m : ℤ) :
    Complex.exp (-(Complex.I*((m : ℝ)*Real.pi))) = (-1 : ℂ)^m := by
  rw [Complex.exp_neg, integral_frequency_exp, ← inv_zpow, inv_neg_one]

lemma integral_frequency_ne_zero (m : ℤ) (hm : m ≠ 0) :
    Complex.I*((m : ℝ)*Real.pi) ≠ 0 := by
  simpa only [Complex.ofReal_mul] using mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (Int.cast_ne_zero.mpr hm) Real.pi_ne_zero))

/-- Every actual oscillatory moment is represented by one rational polynomial,
independent of the nonzero integer frequency. -/
theorem moment_polynomial_representation (m : ℤ) (hm : m ≠ 0) (r : ℕ) :
    moment ((m : ℝ)*Real.pi) r =
      (-1 : ℂ)^m*(-1)^r*
        (endpointMoment r).eval₂ (Rat.castHom ℂ) (((m : ℝ)*Real.pi)^2) /
          (Complex.I*((m : ℝ)*Real.pi))^(r+1) := by
  have ht := integral_frequency_ne_zero m hm
  have h := exponentialMoment_polynomial _ _ ht
    (integral_frequency_exp m) (integral_frequency_exp_neg m) r
  have hz : -(Complex.I*((m : ℝ)*Real.pi))^2 = (((m : ℝ)*Real.pi)^2 : ℂ) := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hz] at h
  apply (eq_div_iff (pow_ne_zero _ ht)).mpr
  simpa only [moment, Complex.ofReal_mul, mul_comm (exponentialMoment _ _)] using h

end OscillatoryRecurrence
