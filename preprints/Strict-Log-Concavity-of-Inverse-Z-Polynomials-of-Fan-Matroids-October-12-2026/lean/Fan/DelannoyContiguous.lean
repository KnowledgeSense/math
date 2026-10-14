import Fan.DelannoyFactorization

noncomputable section
open Polynomial
open scoped BigOperators
namespace Fan

/-- Coefficients of the normalized primitive of the binomial kernel. -/
def delannoyMeanPolynomial (a b : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (min a b + 1),
    monomial k (((a.choose k : ℝ) * b.choose k) / (k+1))

theorem delannoyMeanPolynomial_coeff (a b k : ℕ) :
    (delannoyMeanPolynomial a b).coeff k = ((a.choose k : ℝ) * b.choose k)/(k+1) := by
  unfold delannoyMeanPolynomial
  simp only [finsetSum_coeff, coeff_monomial]
  by_cases hk : k < min a b + 1
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [hj]
    · simp [hk]
  · have he : a < k ∨ b < k := by omega
    have hc : (a.choose k : ℝ) * b.choose k = 0 := by
      rcases he with he | he <;> simp [Nat.choose_eq_zero_of_lt he]
    rw [hc, zero_div]
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : j ≠ k := by have := Finset.mem_range.mp hj; omega
    simp [hjk]

theorem choose_real_lower (a k : ℕ) :
    ((a+1:ℕ):ℝ) * a.choose k = (((a+1:ℕ):ℝ)-k) * (a+1).choose k := by
  by_cases hk : k ≤ a+1
  · have h := Nat.choose_mul_succ_eq a k
    have hr : (a.choose k:ℝ) * ((a+1:ℕ):ℝ) =
        ((a+1).choose k:ℝ) * ((a+1-k:ℕ):ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub hk] at hr
    nlinarith
  · have ha : a < k := by omega
    have ha1 : a+1 < k := by omega
    simp [Nat.choose_eq_zero_of_lt ha,Nat.choose_eq_zero_of_lt ha1]

theorem choose_real_next (a k : ℕ) :
    ((k+1:ℕ):ℝ) * a.choose (k+1) = ((a:ℝ)-k) * a.choose k := by
  by_cases hk : k ≤ a
  · have h := Nat.choose_succ_right_eq a k
    have hr : (a.choose (k+1):ℝ) * ((k+1:ℕ):ℝ) =
        (a.choose k:ℝ) * ((a-k:ℕ):ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub hk] at hr
    nlinarith
  · have ha : a < k := by omega
    have ha1 : a < k+1 := by omega
    simp [Nat.choose_eq_zero_of_lt ha,Nat.choose_eq_zero_of_lt ha1]

/-- The lowering contiguous relation, without division by the rank parameter. -/
theorem delannoy_lower_left (a b : ℕ) :
    C ((a+1:ℕ):ℝ) * delannoyPolynomial a b =
      C ((a+1:ℕ):ℝ) * delannoyPolynomial (a+1) b -
        X * (delannoyPolynomial (a+1) b).derivative := by
  ext k
  cases k with
  | zero => simp
  | succ k =>
    simp only [coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative, delannoyPolynomial_coeff]
    have h := choose_real_lower a (k+1)
    push_cast at h ⊢
    nlinarith

/-- The raising contiguous relation with the exact normalized primitive. -/
theorem delannoy_raise_left (a b : ℕ) :
    delannoyPolynomial (a+1) b = (1-X)*delannoyPolynomial a b +
      C ((b+1:ℕ):ℝ)*X*delannoyMeanPolynomial a b := by
  ext k
  cases k with
  | zero => simp [sub_mul]
  | succ k =>
    simp only [sub_mul,one_mul,coeff_add,coeff_sub,coeff_X_mul]
    rw [mul_assoc,coeff_C_mul,coeff_X_mul,delannoyMeanPolynomial_coeff]
    simp only [delannoyPolynomial_coeff,Nat.choose_succ_succ,Nat.cast_add]
    have h := choose_real_next b k
    push_cast at h
    have hk : (k:ℝ)+1 ≠ 0 := by positivity
    field_simp
    have hm := congrArg (fun t : ℝ => (a.choose k:ℝ)*t) h
    simp only [Nat.cast_one, Nat.succ_eq_add_one] at hm ⊢
    nlinarith only [hm]

theorem delannoyPolynomial_symm (a b : ℕ) : delannoyPolynomial a b = delannoyPolynomial b a := by
  ext k
  simp only [delannoyPolynomial_coeff]
  ring

theorem delannoyMeanPolynomial_symm (a b : ℕ) :
    delannoyMeanPolynomial a b = delannoyMeanPolynomial b a := by
  ext k
  simp only [delannoyMeanPolynomial_coeff]
  ring

theorem delannoy_coefficient_recurrence (a b k : ℕ) :
    ((k:ℝ)+1)^2 * ((a.choose (k+1):ℝ)*b.choose (k+1)) =
      ((a:ℝ)-k)*((b:ℝ)-k)*((a.choose k:ℝ)*b.choose k) := by
  have ha := choose_real_next a k
  have hb := choose_real_next b k
  push_cast at ha hb
  calc
    _ = (((k:ℝ)+1)*a.choose (k+1))*(((k:ℝ)+1)*b.choose (k+1)) := by ring
    _ = _ := by rw [ha,hb]; ring

/-- The integrated differential equation for the exact binomial polynomial. -/
theorem delannoy_integrated_equation (a b : ℕ) :
    (1-X)*(delannoyPolynomial a b).derivative +
      C ((a:ℝ)+b+1)*delannoyPolynomial a b =
        C (((a:ℝ)+1)*((b:ℝ)+1))*delannoyMeanPolynomial a b := by
  ext k
  cases k with
  | zero =>
    simp [sub_mul,coeff_derivative,delannoyPolynomial_coeff,delannoyMeanPolynomial_coeff]
    ring
  | succ k =>
    simp only [sub_mul,one_mul,coeff_add,coeff_sub,coeff_X_mul,coeff_C_mul,
      coeff_derivative,delannoyPolynomial_coeff,delannoyMeanPolynomial_coeff]
    have h := delannoy_coefficient_recurrence a b (k+1)
    push_cast at h ⊢
    have hk : (k:ℝ)+1+1 ≠ 0 := by positivity
    field_simp
    nlinarith only [h]

theorem delannoy_mean_derivative (a b : ℕ) :
    X*(delannoyMeanPolynomial a b).derivative + delannoyMeanPolynomial a b =
      delannoyPolynomial a b := by
  ext k
  cases k with
  | zero => simp [delannoyMeanPolynomial_coeff]
  | succ k =>
    simp only [coeff_add,coeff_X_mul,coeff_derivative,delannoyMeanPolynomial_coeff,
      delannoyPolynomial_coeff]
    push_cast
    have hk : (k:ℝ)+1+1 ≠ 0 := by positivity
    field_simp

/-- The exact hypergeometric differential equation. -/
theorem delannoy_differential_equation (a b : ℕ) :
    X*(1-X)*(delannoyPolynomial a b).derivative.derivative +
      (1+C ((a:ℝ)+b-1)*X)*(delannoyPolynomial a b).derivative -
      C ((a:ℝ)*b)*delannoyPolynomial a b = 0 := by
  have hI := delannoy_integrated_equation a b
  have hM := delannoy_mean_derivative a b
  have hD := congrArg derivative hI
  simp only [derivative_add,derivative_sub,derivative_mul,derivative_one,derivative_X,
    derivative_C,zero_mul,zero_sub,zero_add] at hD
  simp only [map_add,map_mul,map_sub,map_one] at hI hD ⊢
  linear_combination X*hD + hI + (C (a:ℝ)+1)*(C (b:ℝ)+1)*hM

end Fan
