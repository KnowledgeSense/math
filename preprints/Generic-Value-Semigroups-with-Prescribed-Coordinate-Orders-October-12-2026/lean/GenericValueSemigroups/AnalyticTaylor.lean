import GenericValueSemigroups.AnalyticValues

open Filter
open scoped Topology BigOperators

namespace GenericValueSemigroups

/-- The ordinary Taylor power series at the origin, defined from actual complex derivatives. -/
noncomputable def analyticTaylor (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => iteratedDeriv n f 0 / (n.factorial : ℂ))

@[simp] theorem coeff_analyticTaylor (f : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (analyticTaylor f) = iteratedDeriv n f 0 / (n.factorial : ℂ) :=
  PowerSeries.coeff_mk n _

@[simp] theorem constantCoeff_analyticTaylor (f : ℂ → ℂ) :
    (analyticTaylor f).constantCoeff = f 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_analyticTaylor]
  simp

@[simp] theorem analyticTaylor_const (c : ℂ) :
    analyticTaylor (fun _ => c) = PowerSeries.C c := by
  ext n
  by_cases hn : n = 0 <;> simp [iteratedDeriv_const, PowerSeries.coeff_C, hn]

/-- Taylor expansion respects addition, with the required analytic hypotheses. -/
theorem analyticTaylor_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    analyticTaylor (fun t => f t + g t) = analyticTaylor f + analyticTaylor g := by
  ext n
  simp only [coeff_analyticTaylor, map_add,
    iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, add_div]

/-- Taylor expansion respects multiplication by the actual analytic Leibniz formula. -/
theorem analyticTaylor_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    analyticTaylor (fun t => f t * g t) = analyticTaylor f * analyticTaylor g := by
  ext n
  rw [coeff_analyticTaylor, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [coeff_analyticTaylor]
  have hi' : i ≤ n := Finset.mem_range_succ_iff.mp hi
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hi0 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hni : ((n-i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n-i).factorial_ne_zero
  have hchoose : (n.choose i : ℂ) * i.factorial * (n-i).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  field_simp
  linear_combination (iteratedDeriv i f 0 * iteratedDeriv (n-i) g 0) * hchoose

/-- Actual polynomial evaluation and substitution of actual Taylor series agree coefficientwise. -/
theorem analyticTaylor_eval_polynomial {d : ℕ} {F : ℂ → Fin d → ℂ}
    (hF : ∀ i, AnalyticAt ℂ (fun t => F t i) 0) (P : MvPolynomial (Fin d) ℂ) :
    analyticTaylor (fun t => MvPolynomial.eval (F t) P) =
      MvPolynomial.aeval (fun i => analyticTaylor (fun t => F t i)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.eval_C, analyticTaylor_const, MvPolynomial.aeval_C]; rfl
  | add p q hp hq =>
    simp only [map_add]
    rw [analyticTaylor_add (analyticAt_eval_polynomial hF p) (analyticAt_eval_polynomial hF q), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.aeval_X]
    rw [analyticTaylor_mul (analyticAt_eval_polynomial hF p) (hF i), hp]

/-- The analytic order and the formal order of the derivative-defined Taylor series coincide. -/
theorem order_analyticTaylor {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    PowerSeries.order (analyticTaylor f) = analyticOrderAt f 0 := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  constructor
  · intro h i hi
    have hc := PowerSeries.coeff_of_lt_order (φ := analyticTaylor f) i
      (lt_of_lt_of_le (by exact_mod_cast hi) h)
    simpa [Nat.factorial_ne_zero] using hc
  · intro h
    apply PowerSeries.nat_le_order
    intro i hi
    simp [h i hi]

/-- The convergent analytic algebra has exactly the values of the formal algebra of the
actual Taylor series of its coordinate functions. -/
theorem analyticValues_eq_formalValues {d : ℕ} (F : ℂ → Fin d → ℂ)
    (hF : ∀ i, AnalyticAt ℂ (fun t => F t i) 0) (hF0 : F 0 = 0) :
    analyticValues F = formalValues (fun i => analyticTaylor (fun t => F t i)) := by
  rw [analyticValues_eq_analyticPolynomialValues F hF hF0,
    formalValues_eq_polynomialValues _ (fun i => by simp [congrFun hF0 i])]
  ext n
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨P, ?_⟩
    rw [← analyticTaylor_eval_polynomial hF P, order_analyticTaylor (analyticAt_eval_polynomial hF P)]
    exact hP
  · rintro ⟨P, hP⟩
    refine ⟨P, ?_⟩
    rw [← analyticTaylor_eval_polynomial hF P, order_analyticTaylor (analyticAt_eval_polynomial hF P)] at hP
    exact hP

/-- The derivative-defined coefficients agree with every genuine convergent power-series
representation; the formal Taylor series is therefore independent of representation choices. -/
theorem analyticTaylor_coeff_eq_of_hasFPowerSeriesAt {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt f p 0) (n : ℕ) :
    PowerSeries.coeff n (analyticTaylor f) = p.coeff n := by
  obtain ⟨r, hr⟩ := hp
  rw [coeff_analyticTaylor, div_eq_iff (by exact_mod_cast n.factorial_ne_zero)]
  have hh := hr.factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at hh
  have hh' : iteratedDeriv n f 0 = (n.factorial : ℂ) * p.coeff n := by
    simpa only [Finset.prod_const_one, one_smul, nsmul_eq_mul, FormalMultilinearSeries.coeff, Pi.one_def] using hh.symm
  exact hh'.trans (mul_comm _ _)

/-- An analytic error of order at least `N` gives equality of all actual Taylor coefficients
strictly below `N`. -/
theorem analyticTaylor_jet_eq_of_order {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (N : ℕ)
    (horder : (N : ℕ∞) ≤ analyticOrderAt (fun t => f t - g t) 0) :
    formalJet N (analyticTaylor f) = formalJet N (analyticTaylor g) := by
  ext j
  have hj := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hf.fun_sub hg)).mp horder j.val j.isLt
  rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, sub_eq_zero] at hj
  change PowerSeries.coeff j.val (analyticTaylor f) = PowerSeries.coeff j.val (analyticTaylor g)
  simp only [coeff_analyticTaylor, hj]

/-- Coefficientwise version of the convergent finite-jet bridge, using the specified genuine
multilinear Taylor expansion of the outer analytic function. -/
theorem analytic_substitution_finite_jet {d : ℕ} {F : ℂ → Fin d → ℂ}
    (hF : ∀ i, AnalyticAt ℂ (fun t => F t i) 0) (hF0 : F 0 = 0)
    {G : (Fin d → ℂ) → ℂ} {p : FormalMultilinearSeries ℂ (Fin d → ℂ) ℂ}
    (hp : HasFPowerSeriesAt G p 0) (N : ℕ) :
    formalJet N (analyticTaylor (fun t => G (F t))) =
      formalJet N (MvPolynomial.aeval (fun i => analyticTaylor (fun t => F t i))
        (taylorPolynomial p N)) := by
  rw [← analyticTaylor_eval_polynomial hF]
  apply analyticTaylor_jet_eq_of_order
  · exact (hF0 ▸ hp.analyticAt).comp (AnalyticAt.pi hF)
  · exact analyticAt_eval_polynomial hF _
  · exact analytic_substitution_taylor_error hF hF0 hp N

end GenericValueSemigroups
