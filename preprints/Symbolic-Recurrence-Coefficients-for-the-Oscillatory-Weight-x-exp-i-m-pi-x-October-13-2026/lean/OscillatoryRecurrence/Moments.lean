import OscillatoryRecurrence.Definitions

noncomputable section
namespace OscillatoryRecurrence

lemma exponentialMoment_integrable (t : ℂ) (k : ℕ) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ)^k * Complex.exp (t*x))
      MeasureTheory.volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

lemma exponentialMoment_zero (t : ℂ) (ht : t ≠ 0) :
    exponentialMoment t 0 = (Complex.exp t - Complex.exp (-t)) / t := by
  simpa [exponentialMoment] using integral_exp_mul_complex (a := (-1 : ℝ)) (b := 1) ht

lemma exponentialMoment_recurrence (t : ℂ) (k : ℕ) :
    t * exponentialMoment t (k+1) + (k+1) * exponentialMoment t k =
      Complex.exp t - (-1 : ℂ)^(k+1)*Complex.exp (-t) := by
  have hd (x : ℝ) : HasDerivAt
      (fun y : ℝ => (y : ℂ)^(k+1)*Complex.exp (t*y))
      ((k+1)*(x : ℂ)^k*Complex.exp (t*x) + t*((x : ℂ)^(k+1)*Complex.exp (t*x))) x := by
    have h := (((hasDerivAt_id (x : ℂ)).pow (k+1)).mul
      ((Complex.hasDerivAt_exp _).comp (x : ℂ) ((hasDerivAt_id _).const_mul t))).comp_ofReal
    convert h using 1 <;> simp
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ Set.uIcc (-1 : ℝ) 1) => hd x)
    (show IntervalIntegrable (fun x : ℝ =>
      (k+1)*(x : ℂ)^k*Complex.exp (t*x) + t*((x : ℂ)^(k+1)*Complex.exp (t*x)))
      MeasureTheory.volume (-1) 1 from by apply Continuous.intervalIntegrable; fun_prop)
  have hleft : (fun x : ℝ => (k+1)*(x : ℂ)^k*Complex.exp (t*x)) =
      (fun x : ℝ => (k+1)*((x : ℂ)^k*Complex.exp (t*x))) := by funext x; ring
  rw [intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), hleft,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  simpa [exponentialMoment, add_comm] using hi

end OscillatoryRecurrence
